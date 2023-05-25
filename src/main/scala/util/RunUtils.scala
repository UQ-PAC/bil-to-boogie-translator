package util
import analysis.*
import analysis.util.SSA
import cfg_visualiser.{OtherOutput, Output, OutputKindE}
import bap.*
import ir.*
import boogie.*
import specification.*
import BilParser.*
import org.antlr.v4.runtime.tree.ParseTreeWalker
import org.antlr.v4.runtime.{CharStreams, CommonTokenStream}
import translating.*

import java.io.{File, PrintWriter}
import java.io.{BufferedWriter, FileWriter, IOException}
import scala.jdk.CollectionConverters.*
import analysis.solvers.*

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.ArrayBuffer
object RunUtils {
  var globals_ToUSE: Set[SpecGlobal] = Set()
  var internalFunctions_ToUSE: Set[InternalFunction] = Set()
  var globalsOffsets_ToUSE: Map[BigInt, BigInt] = Map()
  var memoryRegionAnalysisResults = None: Option[Map[CfgNode, _]]

  // ids reserved by boogie
  val reserved: Set[String] = Set("free")

  def generateVCsAdt(fileName: String, elfFileName: String, specFileName: Option[String], performAnalysis: Boolean, performInterpret: Boolean): BProgram = {

    val adtLexer = BilAdtLexer(CharStreams.fromFileName(fileName))
    val tokens = CommonTokenStream(adtLexer)
    // ADT
    val parser = BilAdtParser(tokens)

    parser.setBuildParseTree(true)

    val program = AdtStatementLoader.visitProject(parser.project())

    val elfLexer = SymsLexer(CharStreams.fromFileName(elfFileName))
    val elfTokens = CommonTokenStream(elfLexer)
    val elfParser = SymsParser(elfTokens)
    elfParser.setBuildParseTree(true)

    val (externalFunctions, globals, globalOffsets, internalFunctions) = ElfLoader.visitSyms(elfParser.syms())
    print(internalFunctions)
    if (performAnalysis) {
      globals_ToUSE = globals
      globalsOffsets_ToUSE = globalOffsets
      internalFunctions_ToUSE = internalFunctions
      print("\nInternal: \n")
      print(internalFunctions)
      print("\nGlobals: \n")
      print(globals)
      print("\nGlobal Offsets: \n")
      print(globalOffsets)
    }

    //println(globalOffsets)
    //val procmap = program.subroutines.map(s => (s.name, s.address)).toMap
    //println(procmap)
    //println(externalFunctions)
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

    //val externalRemover = ExternalRemover(externalNames)
    val renamer = Renamer(reserved)
    //IRProgram = externalRemover.visitProgram(IRProgram)
    IRProgram = renamer.visitProgram(IRProgram)

    //IRProgram.stripUnreachableFunctions()

    if (performAnalysis) {
//      print("\n\n\n\n"+{IRProgram.procedures}+"\n\n\n\n")
      analyse(IRProgram)
    }

    val boogieTranslator = IRToBoogie(IRProgram, specification)
    boogieTranslator.translate
  }

  def analyse(IRProgram: Program): Unit = {
    //    val wcfg = IntraproceduralProgramCfg.generateFromProgram(program)
    //
    ////    //print(wcfg.nodes)
    ////    Output.output(OtherOutput(OutputKindE.cfg), wcfg.toDot({ x =>
    ////      x.toString
    ////    }, Output.dotIder))
    //
    //
    //    val an = ConstantPropagationAnalysis.WorklistSolver(wcfg)
    //    val res = an.analyze().asInstanceOf[Map[CfgNode, _]]
    //    print(res.keys)
    //    Output.output(OtherOutput(OutputKindE.cfg), an.cfg.toDot(Output.labeler(res, an.stateAfterNode), Output.dotIder))

    val cfg = IntraproceduralProgramCfg.generateFromProgram(IRProgram)
    //    Output.output(OtherOutput(OutputKindE.cfg), cfg.toDot({ x =>
    //      x.toString
    //    }, Output.dotIder))


//    val solver = new ConstantPropagationAnalysis.WorklistSolver(cfg)
//    val result = solver.analyze()
//    Output.output(OtherOutput(OutputKindE.cfg), cfg.toDot(Output.labeler(result, solver.stateAfterNode), Output.dotIder))
//
//    dump_file(cfg.getEdges.toString(), "result")
//
//    print(s"\n Constant prop results\n ****************\n  ${result.values}  \n *****************\n")


    //    val solver2 = new SteensgaardAnalysis(translator.program, result)
    //    val result2 = solver2.analyze()
    //    print(solver2.pointsTo())

//    val ssa = new SSA(cfg)
//    ssa.analyze()


    /*
    TODO - solveMemory parameters not set
    val solver3 = new MemoryRegionAnalysis(cfg)
    val result3 = solver3.analyze()
    print(solver3.solveMemory())
    val stringBuilder: StringBuilder = new StringBuilder()
    stringBuilder.append("digraph G {\n")
    for ((k, v) <- solver3.solveMemory()) {
      v.foreach(x => stringBuilder.append(s"\"${k}\" -> \"${x}\";\n"))
    }
    stringBuilder.append("}")
    dump_plot(stringBuilder.toString(), "result")
    */

//    val solver2 = new MemoryRegionAnalysis(cfg)
//    val result2 = solver2.analyze()
//    print(s"\n Mem region results\n ****************\n  ${solver2.getMapping}  \n *****************\n")
//    Output.output(OtherOutput(OutputKindE.cfg), cfg.toDot(Output.labeler(solver2.getMapping, solver.stateAfterNode), Output.dotIder))

    val solver2 = new MemoryRegionAnalysis.WorklistSolver(cfg, globals_ToUSE, globalsOffsets_ToUSE)
    val result2 = solver2.analyze()
    memoryRegionAnalysisResults = Some(result2)
    Output.output(OtherOutput(OutputKindE.cfg), cfg.toDot(Output.labeler(result2, solver2.stateAfterNode), Output.dotIder), "mra")


    val mmm = new MemoryModelMap
    mmm.convertMemoryRegions(result2, internalFunctions_ToUSE)
    print("Memory Model Map: \n")
    print(mmm)
    val interprocCfg = InterproceduralProgramCfg.generateFromProgram(IRProgram)
    val solver3 = new analysis.ValueSetAnalysis.WorklistSolver(interprocCfg, globals_ToUSE, internalFunctions_ToUSE, globalsOffsets_ToUSE, mmm)
    val result3 = solver3.analyze()
    Output.output(OtherOutput(OutputKindE.cfg), interprocCfg.toDot(Output.labeler(result3, solver3.stateAfterNode), Output.dotIder), "vsa")
    val newCFG = resolveCFG(interprocCfg, result3.asInstanceOf[Map[CfgNode, Map[Expr, Set[Value]]]], IRProgram)
    Output.output(OtherOutput(OutputKindE.cfg), newCFG.toDot({ x => x.toString}, Output.dotIder), "resolvedCFG")
  }

//  def CFGtoProgram(cfg: InterproceduralProgramCfg, IRProgram: Program): Program = {
//    val newProcedures: ListBuffer[Procedure] = ArrayBuffer[Procedure]()
//
//
//
//
//    Program(IRProgram.procedures, IRProgram.initialMemory)
//  }

  def alterProgram(IRProgram: Program): Program = {
    return IRProgram
  }

  def resolveCFG(interproceduralProgramCfg: InterproceduralProgramCfg, valueSets: Map[CfgNode, Map[Expr, Set[Value]]], IRProgram: Program): InterproceduralProgramCfg = {
    val newBuffer: ListBuffer[CfgNode] = ListBuffer[CfgNode]()
    interproceduralProgramCfg.entries.foreach(
      n => process(n))

    def process(n: CfgNode): Unit = {
      n match
        case commandNode: CfgCommandNode =>
          commandNode.data match
            case indirectCall: IndirectCall =>
                val valueSet: Map[Expr, Set[Value]] = valueSets(n)
                val functionNames = resolveAddresses(valueSet(indirectCall.target))
                //TODO: if this does not work, it means function names should be "l"+name
                functionNames.size match
                  case 0 => newBuffer += n
                  case 1 =>
                    val newDirectCall = CfgCommandNode(CfgNode.nextId(), n.pred, n.succ, DirectCall(IRProgram.procedures.filter(_.name.equals(functionNames.head)).head, indirectCall.condition, indirectCall.returnTarget))
                    newBuffer += newDirectCall
                    fixEdges(n, newDirectCall)
                  case _ =>
                    var lastAdded: Option[CfgCommandNode] = Option.empty[CfgCommandNode]
                    functionNames.foreach(
                      name => {
                        val newDirectCall = CfgCommandNode(CfgNode.nextId(), n.pred, n.succ, DirectCall(IRProgram.procedures.filter(_.name.equals(name)).head, indirectCall.condition, indirectCall.returnTarget))
                        newBuffer += newDirectCall
                        fixEdges(n, newDirectCall)
                        lastAdded match
                          case Some(last) =>
                            last.succ.add(newDirectCall)
                            newDirectCall.pred.add(last)
                          case None => ()
                        lastAdded = Some(newDirectCall)
                      }
                    )
            case _ => newBuffer += n
        case _ => newBuffer += n
    }

    def fixEdges(oldNode: CfgNode, newNode: CfgNode): Unit = {
        oldNode.pred.foreach(
            pred => {
              pred.succ.add(newNode)
              pred.succ.remove(oldNode)
            }
        )
    }

    def nameExists(name: String): Boolean = {
      IRProgram.procedures.exists(_.name.equals(name))
    }

    def resolveAddresses(valueSet: Set[Value]): Set[String] = {
      var functionNames: Set[String] = Set()
      valueSet.foreach {
        case globalAddress: GlobalAddress =>
           if (nameExists(globalAddress.name)) {
             functionNames += globalAddress.name
             print(s"Global address ${globalAddress.name} resolved.\n")
           } else {
             print(s"Global address ${globalAddress.name} does not exist in the program.\n")
           }

        case localAddress: LocalAddress =>
          if (nameExists(localAddress.name)) {
            functionNames += localAddress.name
            print(s"Local address ${localAddress.name} resolved.\n")
          } else {
            print(s"Local address ${localAddress.name} does not exist in the program.\n")
          }
        case _ =>
      }
      functionNames
    }

    interproceduralProgramCfg.entries = newBuffer
    interproceduralProgramCfg
  }

  def writeToFile(program: BProgram, outputFileName: String): Unit = {
    try {
      val writer = new BufferedWriter(new FileWriter(outputFileName, false))
      writer.write(program.toString)
      writer.flush()
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
