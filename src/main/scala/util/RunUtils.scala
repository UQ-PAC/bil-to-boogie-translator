package util
import analysis._
import cfg_visualiser.{OtherOutput, Output, OutputKindE}
import bap._
import ir._
import boogie._
import specification._
import BilParser._
import org.antlr.v4.runtime.tree.ParseTreeWalker
import org.antlr.v4.runtime.{CharStreams, CommonTokenStream}
import translating._

import java.io.{File, PrintWriter}
import java.io.{BufferedWriter, FileWriter, IOException}
import scala.jdk.CollectionConverters._
import analysis.solvers._

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.ArrayBuffer
object RunUtils {
  var memoryRegionAnalysisResults: Option[Map[CfgNode, _]] = None

  // ids reserved by boogie
  val reserved: Set[String] = Set("free")

  def generateVCsAdt(fileName: String, elfFileName: String, specFileName: Option[String], performAnalysis: Boolean, performInterpret: Boolean): BProgram = {

    val adtLexer = BilAdtLexer(CharStreams.fromFileName(fileName))
    val tokens = CommonTokenStream(adtLexer)
    val parser = BilAdtParser(tokens)

    parser.setBuildParseTree(true)

    println("[!] Generating IR")
    val program = AdtStatementLoader.visitProject(parser.project())

    val elfLexer = SymsLexer(CharStreams.fromFileName(elfFileName))
    val elfTokens = CommonTokenStream(elfLexer)
    val elfParser = SymsParser(elfTokens)
    elfParser.setBuildParseTree(true)
    println("[!] Parsing .relf")
    val (externalFunctions, globals, globalOffsets) = ElfLoader.visitSyms(elfParser.syms())

    //println(globalOffsets)
    //val procmap = program.subroutines.map(s => (s.name, s.address)).toMap
    //println(procmap)
    //println(globals)
    /*
    TODO analyses/transformations
    -type checking
    -make sure there's no sneaky stack accesses
    -constant propagation to properly analyse control flow and replace all indirect calls
    -identify external calls
    -check for use of uninitialised registers in procedures to pass them in
    -points to/alias analysis to split memory into separate maps as much as possible? do we want this?
    -make memory reads better?
     */

    val externalNames = externalFunctions.map(e => e.name)

    println("[!] Translating from BAP to IR")
    val IRTranslator = BAPToIR(program)
    var IRProgram = IRTranslator.translate

    val specification = specFileName match {
      case Some(s) => val specLexer = SpecificationsLexer(CharStreams.fromFileName(s))
        val specTokens = CommonTokenStream(specLexer)
        val specParser = SpecificationsParser(specTokens)
        specParser.setBuildParseTree(true)
        val specLoader = SpecificationLoader(globals, IRProgram)
        specLoader.visitSpecification(specParser.specification())
      case None => Specification(globals, Map(), List(), List(), List())
    }

    if (performInterpret) {
      Interpret(IRProgram)
    }

    println("[!] Removing external function calls")
    // Remove external function references (e.g. @printf)
    val externalRemover = ExternalRemover(externalNames)
    // Removes BAP naming artefacts (e.g. # preceding variable names)
    val renamer = Renamer(reserved)
    IRProgram = externalRemover.visitProgram(IRProgram)
    IRProgram = renamer.visitProgram(IRProgram)

    if (performAnalysis) {
      analyse(IRProgram, externalFunctions, globals, globalOffsets)
    }

    IRProgram.stripUnreachableFunctions()

    println("[!] Translating to Boogie")
    val boogieTranslator = IRToBoogie(IRProgram, specification)
    println("[!] Done! Exiting...")
    boogieTranslator.translate
  }

  def analyse(IRProgram: Program, externalFunctions: Set[ExternalFunction], globals: Set[SpecGlobal], globalOffsets: Map[BigInt, BigInt]): Unit = {
    val subroutines = IRProgram.procedures.filter(p => p.address.isDefined).map{(p: Procedure) => BigInt(p.address.get) -> p.name}.toMap
    val globalAddresses = globals.map{(s: SpecGlobal) => s.address -> s.name}.toMap
    val externalAddresses = externalFunctions.map{(e: ExternalFunction) => e.offset -> e.name}.toMap
    println("Globals:" )
    println(globalAddresses)
    println("Global Offsets: ")
    println(globalOffsets)
    println("External: ")
    println(externalAddresses)
    println("Subroutine Addresses:")
    println(subroutines)

    val cfg = ProgramCfg.fromIR(IRProgram, inlineLimit = 0)

    println("[!] Running Constant Propagation")
    val solver = ConstantPropagationAnalysis.WorklistSolver(cfg)
    val result = solver.analyze(true).asInstanceOf[Map[CfgNode, Map[Variable, Any]]]
    Output.output(OtherOutput(OutputKindE.cfg), cfg.toDot(Output.labeler(result, solver.stateAfterNode), Output.dotIder), "cpa")

    println("[!] Running MRA")
    val solver2 = MemoryRegionAnalysis.WorklistSolver(cfg, globalAddresses, globalOffsets, subroutines, result)
    val result2 = solver2.analyze(true).asInstanceOf[Map[CfgNode, MemoryRegion]]
    memoryRegionAnalysisResults = Some(result2)
    Output.output(OtherOutput(OutputKindE.cfg), cfg.toDot(Output.labeler(result2, solver2.stateAfterNode), Output.dotIder), "mra")

    println("[!] Running MMM")
    val mmm = MemoryModelMap()
    mmm.convertMemoryRegions(result2, externalAddresses)

    println("[!] Running VSA")
    val solver3 = ValueSetAnalysis.WorklistSolver(cfg, globalAddresses, externalAddresses, globalOffsets, subroutines, mmm, result)
    val result3 = solver3.analyze(false)
    Output.output(OtherOutput(OutputKindE.cfg), cfg.toDot(Output.labeler(result3, solver3.stateAfterNode), Output.dotIder), "vsa")

    println("[!] Resolving CFG")
    val newCFG = ProgramCfg.fromIR(resolveCFG(cfg, result3.asInstanceOf[Map[CfgNode, Map[Expr, Set[Value]]]], IRProgram), inlineLimit = 0)
    Output.output(OtherOutput(OutputKindE.cfg), newCFG.toDot(x => x.toString, Output.dotIder), "resolvedCFG")
  }

  def resolveCFG(cfg: ProgramCfg, valueSets: Map[CfgNode, Map[Expr, Set[Value]]], IRProgram: Program): Program = {
    cfg.nodes.foreach(n => process(n))

    def process(n: CfgNode): Unit = n match {
      case commandNode: CfgCommandNode =>
        commandNode.data match
          case indirectCall: IndirectCall =>
            val valueSet: Map[Expr, Set[Value]] = valueSets(n)
            val functionNames = resolveAddresses(valueSet(indirectCall.target))
            if (functionNames.size == 1) {
              commandNode.block match
                case block: Block =>
                  block.jumps = block.jumps.filter(!_.equals(indirectCall))
                  block.jumps += DirectCall(IRProgram.procedures.filter(_.name.equals(functionNames.head.name)).head, indirectCall.condition, indirectCall.returnTarget)
                case null => throw new Exception("Node not found in nodeToBlock map")
            } else {
              functionNames.foreach(addressValue =>
                commandNode.block match
                  case block: Block =>
                    block.jumps = block.jumps.filter(!_.equals(indirectCall))
                    if (indirectCall.condition.isDefined) {
                      block.jumps += DirectCall(IRProgram.procedures.filter(_.name.equals(addressValue.name)).head, Option(BinaryExpr(BVAND, indirectCall.condition.get, BinaryExpr(BVEQ, indirectCall.target, addressValue.expr))), indirectCall.returnTarget)
                    } else {
                      block.jumps += DirectCall(IRProgram.procedures.filter(_.name.equals(addressValue.name)).head, Option(BinaryExpr(BVEQ, indirectCall.target, addressValue.expr)), indirectCall.returnTarget)
                    }
                  case null => throw new Exception("Node not found in nodeToBlock map")
              )
            }
          case _ =>
      case _ =>
    }

    def nameExists(name: String): Boolean = {
      IRProgram.procedures.exists(_.name.equals(name))
    }

    def addFakeProcedure(name: String): Unit = {
      IRProgram.procedures += Procedure(name, None, ArrayBuffer(), ArrayBuffer(), ArrayBuffer())
    }

    def resolveAddresses(valueSet: Set[Value]): Set[AddressValue] = {
      var functionNames: Set[AddressValue] = Set()
      valueSet.foreach {
        case globalAddress: GlobalAddress =>
          if (nameExists(globalAddress.name)) {
            functionNames += globalAddress
            println(s"RESOLVED: Call to Global address ${globalAddress.name} resolved.")
          } else {
            addFakeProcedure(globalAddress.name)
            functionNames += globalAddress
            println(s"Global address ${globalAddress.name} does not exist in the program.  Added a fake function.")
          }
        case localAddress: LocalAddress =>
          if (nameExists(localAddress.name)) {
            functionNames += localAddress
            println(s"RESOLVED: Call to Local address ${localAddress.name}")
          } else {
            addFakeProcedure(localAddress.name)
            functionNames += localAddress
            println(s"Local address ${localAddress.name} does not exist in the program. Added a fake function.")
          }
        case _ =>
      }
      functionNames
    }
    IRProgram
  }

  def writeToFile(program: BProgram, outputFileName: String): Unit = {
    try {
      val writer = BufferedWriter(FileWriter(outputFileName, false))
      writer.write(program.toString)
      writer.flush()
      writer.close()
    } catch {
      case _: IOException => System.err.println("Error writing to file.")
    }
  }

  def dump_file(content: String, name: String): Unit = {
    val outFile = new File(s"${name}.txt")
    val pw = new PrintWriter(outFile, "UTF-8")
    pw.write(content)
    pw.close()
  }

  def dump_plot(content: String, name: String): Unit = {
    val outFile = new File(s"${name}.dot")
    val pw = new PrintWriter(outFile, "UTF-8")
    pw.write(content)
    pw.close()
  }

}

class AnalysisTypeException(message: String)
  extends Exception("Tried to operate on two analyses of different types: " + message) {

  def this(message: String, cause: Throwable) = {
    this(message)
    initCause(cause)
  }
}

class AssumptionViolationException(message: String) extends Exception("Assumption Violation: " + message) {

  def this(message: String, cause: Throwable) = {
    this(message)
    initCause(cause)
  }
}

class LatticeViolationException(message: String)
    extends Exception("A lattice transfer function broke monotonicity: " + message) {

  def this(message: String, cause: Throwable) = {
    this(message)
    initCause(cause)
  }
}

class SegmentationViolationException(message: String)
    extends Exception("The code attempts to dereference a pointer we don't know about: " + message) {

  def this(message: String, cause: Throwable) = {
    this(message)
    initCause(cause)
  }
}
