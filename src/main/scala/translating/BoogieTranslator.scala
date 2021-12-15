package translating

import astnodes.exp.{BinOp, BinOperator, Concat, Expr, Literal, MemLoad, MemStore, UniOp, UniOperator, Var}
import astnodes.stmt.assign.{Assign, MemAssign, RegisterAssign}
import astnodes.stmt.*
import astnodes.parameters.{InParameter, OutParameter}
import astnodes.Label
import translating.FlowGraph

import scala.collection.mutable.HashSet
import java.io.{BufferedWriter, FileWriter, IOException}
import scala.collection.immutable
// import java.util
import java.util.stream.Collectors
import java.util.{ArrayList, HashMap, HashSet, LinkedList, List, Map, Objects, Set}
import scala.collection.mutable
import scala.jdk.CollectionConverters.*
import util.AssumptionViolationException

// TODO rewrite this file to make the flowGraph immutable (this should make whats happening a bit more transparent)
class BoogieTranslator(flowGraph: FlowGraph, outputFileName: String) {
  private var uniqueInt = 0;

  /** Starting point for a BIL translation.
    */
  def translate(): FlowGraph = {
    createLabels()
    optimiseSkips()
    identifyImplicitParams()
    resolveInParams()
    resolveOutParams()
    // TODO this doesnt work: resolveVars()
    addVarDeclarations(flowGraph.types)
    inferConstantTypes()
    // TODO could turn this on later:  replaceGlobalVars(symbolTable)
    // writeToFile()

    flowGraph;
  }

  private def createLabels(): Unit = {
    val lines = flowGraph.getLines
    val usedLabels = new mutable.HashSet[String]

    // get all referred labels within the flow graph
    lines.forEach(line => {
      val target = getJumpTarget(line)
      if (target != null) usedLabels.add(target)
    })

    // show all labels which are referred; hide all labels which are not
    lines.forEach(line => {
      val label = line.getLabel
      if (usedLabels.contains(label.getPc)) label.show()
      else label.hide()
    })
  }

  // target labels are used in jumps and cjumps
  private def getJumpTarget(fact: Stmt): String = fact match {
    case jmpStmt: JmpStmt => jmpStmt.target
    case cjmpStmt: CJmpStmt => cjmpStmt.trueTarget // TODO and falseTarget
    case _ => null
  }

  /** If a skip is not jumped to, we should remove it. Depends on:
    *   - {@link #createLabels ( )}
    */
  private def optimiseSkips(): Unit = {
    flowGraph.getLines.forEach(line => {
      if (line.isInstanceOf[SkipStmt]) flowGraph.removeLine(line)
    })
  }

  /** Many facts.parameters are implicit in BIL, represented not as statements but as a particular pattern of loading
    * registers which have not been previously assigned within the function to memory addresses based on the SP, at the
    * beginning of the function. This method identifies this pattern and adds any facts.parameters found to the
    * function's parameter list. It is assumed that out-facts.parameters are always explicitly stated in BIL, and
    * therefore translating.StatementLoader would have added them already. It is assumed that the first block (i.e. root
    * block) of any function will contain all loadings of facts.parameters.
    *
    * We assume that these store instructions contain only the register on the rhs. We also assume that identical memory
    * accesses (e.g. mem[2]) are never written differently (e.g. mem[1+1]), as this is what we use for identifying and
    * substituting implicit facts.parameters. We assume that these registers are only accessed once - i.e. by the store
    * instruction - before they are assigned.
    */
  private def identifyImplicitParams(): Unit = {
    flowGraph.getFunctions.forEach(function => {
        val params = function.getHeader.getInParams
        val rootBlock = function.getBlocks.get(0)
        val assignedRegisters = new mutable.HashSet[Var]

      // TODO could neaten this further with case classes by combiling the nested matches
        rootBlock.getLines.forEach(line => {line match {
          case store: MemAssign => store.getRhs match {
            case rhsVar: Var if (isRegister(rhsVar) && assignedRegisters.contains(rhsVar)) =>
              val param = new InParameter(new Var(uniqueVarName, rhsVar.size), rhsVar)
              param.setAlias(store.getLhs.asInstanceOf[MemLoad])
              params.add(param)
            case _ =>
          }
          case assign: Assign => assign.getLhs match {
            case lhsVar: Var if (isRegister(lhsVar)) => assignedRegisters.add(lhsVar)
            case _: Var =>
          }
          case _ =>
        }})

        removeDuplicateParamsAndMerge(params)
        createCallArguments(function.getHeader)
      })
  }

  /** Implicit params found may contain params already listed explicitly. If so, we take the var name of the explicit
    * param, and the alias of the implicit param.
    */
  private def removeDuplicateParamsAndMerge(params: List[InParameter]): Unit = {
    val iter = params.iterator
    while (iter.hasNext) {
      val param = iter.next

      val otherparams = params.asScala.filter(otherParam => {
        (param != otherParam) && param.getRegister == otherParam.getRegister
      })
      
      otherparams.foreach{
        case x if (x.getAlias == null) => x.setName(param.getName)  // null alias => this is the explicit param
        case x => x.setAlias(param.getAlias)  // non-null alias => this is the implicit param
      }
      
      if (otherparams.nonEmpty) iter.remove()
    }
  }

  /** Provides function calls with a list of the facts.parameters they will need to provide arguments for.
    */
  private def createCallArguments(func: EnterSub): Unit =
    flowGraph.getLines.asScala.filter(line => line match {
      case callStmt: CallStmt if (callStmt.funcName == func.getFuncName) => true
      case _ => false
    }).asJava.asInstanceOf[List[CallStmt]].forEach(call =>
      func.getInParams.forEach((param: InParameter) => call.getArgs.add(param.getRegister))
    )

  /** We want to replace mem expressions which represent facts.parameters, like mem[SP + 1], with the human-readable
    * names of those facts.parameters. We do this by first removing the initialising store fact "mem[SP + 1] := X0",
    * then replacing all instances of "mem[SP + 1]" with the variable name. Depends on:
    *   - {@link #identifyImplicitParams ( )} Assumes:
    *   - Registers on the RHS of the initialising store fact are reassigned before they are used again.
    *   - No parameter is initialised twice (i.e. there is no more than one initialising store fact per mem facts.exp).
    *   - Equivalent mem expressions are never written differently, e.g. mem[SP + 1] is never written as mem[SP + 0 +
    *     1].
    *   - SP is equivalent at every line of code in the function, except the beginning and end.
    *   - All parameter initialisations occur in the first block of the function.
    *   - ...plus many other assumptions.
    */
  private def resolveInParams(): Unit = {
    flowGraph.getFunctions.forEach(function => {
      // get all InParameters that have been assigned aliases
      val paramsWithAliases = function.getHeader.getInParams.asScala.filter(param => param.getAlias != null)

      // remove all parameter initialisations from the first block
      val forRemoval: List[Stmt] = new ArrayList[Stmt]
      val rootBlock: FlowGraph.Block = function.getBlocks.get(0)

      rootBlock.getLines.forEach(line => {line match {
        case store: MemAssign => (store.getRhs, store.getLhs) match {
          case (rhs: Var, lhs: MemLoad) =>
            for (param <- paramsWithAliases) {
              if (param.getAlias == lhs && param.getRegister == rhs)
                forRemoval.add(line)
            }
          case (_: Var, _) => ??? // We may need to handle this later
          case _ =>
        }
        case _ =>
      }})

      forRemoval.forEach(rootBlock.removeLine)

      // replace all instances of the alias with the human readable parameter name
      for (param <- paramsWithAliases) {
        function.getLines.forEach(line =>
          replaceAllMatchingChildren(line, param.getAlias, param.getName)
        )
      }
    })
  }

  // todo: this seems to produce a list with duplicates
  private def getLocalVarsInFunction(function: FlowGraph.Function) = {
    val vars = new mutable.HashSet[Var]
    function.getLines.forEach(line => {
      if (line.isInstanceOf[RegisterAssign]) {
        val lhs = line.asInstanceOf[Assign].getLhs.asInstanceOf[Var]
        // TODO slow
        if (
          flowGraph.getGlobalInits.stream.noneMatch(init => init.variable.name == lhs.name)
          && function.getHeader.getInParams.stream.noneMatch((inParam) => inParam.getName.name == lhs.name) // TODO check if this is needed
          && !(function.getHeader.getOutParam.get.getName.name == lhs.name)
          && function.getInitStmts.stream.noneMatch(init => init.variable.name == lhs.name)
        ) {
          vars.add(lhs)
        }
      }
    })
    vars.toList
  }

  /** In boogie, all local variables seem to want to be initialised at the beginning of functions. Do we want to make
    * all registers local variables? This should be done before memFacts are replaced by global variables, or the global
    * variables will have var initialisations. Depends on:
    *   - resolveRegisters()
    */
  private def addVarDeclarations(types: immutable.Map[String, Int]): Unit = {
    flowGraph.getFunctions.forEach(function =>
      for (localVar <- getLocalVarsInFunction(function)) {
        // TODO i think this could be replaced by a none label as well
        // TODO rework how this works to instead store a list of vars
        if (!function.getInitStmts.asScala.exists(x => x.variable == localVar)) function.addInitStmt(new InitStmt(localVar, uniqueLabel, s"bv${types(localVar.name)}"))
      }
    )
  }

  private def isRegister(varFact: Var): Boolean = varFact.name.charAt(0) == 'X'

  /** Resolves outParams by crudely replacing all references to their associated register with their human-readable
    * name.
    */
  private def resolveOutParams(): Unit =
    // TODO not sure if this actually helps with readability

    flowGraph.getFunctions.forEach(function =>
      val outParamOp = function.getHeader.getOutParam
      // TODO check will not be necassary if outparam is a scala class
      if (outParamOp.isDefined)
        val outParam = outParamOp.get

        function.getLines.forEach((line: Stmt) =>
          replaceAllMatchingChildren(
            line,
            outParam.getRegister,
            outParam.getName
          )
        )
    )

  private def resolveVars(): Unit =
    flowGraph.getFunctions.forEach(function =>
      function.getBlocks.forEach(block => constantPropagation(block))
    )

  // TODO this should be changed to use a fixed-point algorithm (to make it more accurate)
  /** Performs constant propagation on a list of facts. Modifies the list it is given.
    *
    * Algorithm: For each line, from top to bottom: If the line is an assignment with a pending-removal variable on the
    * lhs, remove the pending-removal line. Then, with the exception of the LHS of assignments, replace any instances of
    * variables with their mapped values, if such a mapping exists. Then, if the result is an assignment with no
    * variables on the RHS, compute the value of the RHS, assign it to the values map and add the line for
    * pending-removal.
    */
  private def constantPropagation(block: FlowGraph.Block): Unit = { // these mapped ExpFacts are expected to only contain literals
    val lines: List[Stmt] = block.getLines
    val values = new HashMap[Var, Literal]
    // assignments that will be removed if the lhs variable is re-assigned later
    val pendingRemoval = new HashMap[Var, Assign]
    // list of lines that will be removed once the loop exits
    val toRemove = new ArrayList[Assign]
    lines.forEach {
      // with the exception of the lhs of assignments, replace any instances of variables with their mapped values
      // note that we don't make an exception for store assignments because their lhs is always a memFact, not var
      case assignment: Assign => {
        // if this is an assignment, remove any assignments that pending removal, that contain this lhs
        values.keySet.forEach(variable => {
          // since we can't call replaceAllMatchingChildren on the whole line, we have to perform it on the rhs manually
          replaceAllMatchingChildren(assignment.getRhs, variable, values.get(variable))
          if (assignment.getRhs == variable) assignment.replace(variable, values.get(variable))
        }
        )

        if (assignment.getLhs.isInstanceOf[Var]) {
          val variable: Var = assignment.getLhs.asInstanceOf[Var]
          if (pendingRemoval.containsKey(variable)) {
            toRemove.add(pendingRemoval.get(variable))
            pendingRemoval.remove(variable)
          }

          /* if the result has no variables on the rhs, compute the value of the rhs, assign it to
                          the values map and add the line for pending-removal */
          assignment.getRhs match {
            case lit: Literal =>
              val computed = computeLiteral(lit)
              val newLiteral: Literal = new Literal(computed) // TODO are these two lines necassary
              values.put(variable, newLiteral)
              pendingRemoval.put(variable, assignment)
            case _ => // skip
          }
        }
      }
      case line => values.forEach((variable: Var, literal: Literal) => replaceAllMatchingChildren(line, variable, literal))
    }
    toRemove.forEach(block.removeLine)
  }

  private def computeLiteral(exp: Expr): String = exp.toString

  // recursively replaces all children of this fact which match the given fact, with the other given fact
  // works because getChildren returns ExpFacts and ExpFacts override equals(), unlike InstFacts which are inherently
  // unique
  // TODO this operators on stmts and expr
  // TODO move this to the classes (i.e. to stmt and expr)
  private def replaceAllMatchingChildren(parent: Stmt, oldExp: Expr, newExp: Expr): Unit = {
    parent.getChildren.forEach((child: Expr) => replaceAllMatchingChildren(child, oldExp, newExp))
    parent.replace(oldExp, newExp)
  }

  private def replaceAllMatchingChildren(parent: Expr, oldExp: Expr, newExp: Expr): Unit = {
    parent.getChildren.forEach((child: Expr) => replaceAllMatchingChildren(child, oldExp, newExp))
    parent.replace(oldExp, newExp)
  }

  /**
    * Where possible resolves global variables in the heap to their variable name
    */
  /*
  private def replaceGlobalVars (symbolTable: mutable.Map[Literal, Var]): Unit = {
    flowGraph.getFunctions.forEach(func => {
      func.getBlocks.forEach(block => {
        block.setLines(block.getLines.stream.map {
              // TODO fix when we can match on m as well
              // TODO this wont work until we have working constant proportation
          case MemAssign(pc, MemLoad(l : Literal), e) if (!m.onStack) =>
            RegisterAssign(pc, symbolTable.getOrElse(l, throw new AssumptionViolationException("Expected to find global variable in symbol table")), e)
          case x => x
        }.collect(Collectors.toList))
      })
    })

  }
  */

  /**
    * Infers the bv sizes for constants
    */
  private def inferConstantTypes(): Unit = {
    flowGraph.getFunctions.forEach(f => f.getBlocks.forEach(b =>
      b.setLines(b.getLines.asScala.map(inferConstantTypes).asJava)
    ))
  }

  private def inferConstantTypes(stmt: Stmt): Stmt = stmt match {
    case assign: RegisterAssign => assign.copy(expr = inferConstantTypes(assign.expr, assign.lhsExp.size))
    case x => x
  }

  // TODO improve this!!
  // TODO use proper type checking
  private def inferConstantTypes(expr: Expr, size: Option[Int]): Expr = expr match {
    case binOp: BinOp => {
      val inputSize = if (BinOperator.changesSize(binOp.operator)) None else size
      val binOp1 = binOp.copy(firstExp = inferConstantTypes(binOp.firstExp, inputSize), secondExp = inferConstantTypes(binOp.secondExp, inputSize))
      (binOp1.firstExp.size, binOp1.secondExp.size) match {
        case (a: Some[Int], b: Some[Int]) if (a == b) => binOp1
        case (a: Some[Int], b: Some[Int]) if (a != b) => throw new AssumptionViolationException(s"Both sides of binop ($binOp) should have the same size (${binOp1.firstExp}: ${a}, ${binOp1.secondExp}: ${b})")
        case (x: Some[Int], None) => binOp1.copy(secondExp = inferConstantTypes(binOp1.secondExp, x))
        case (None, x: Some[Int]) => binOp1.copy(firstExp = inferConstantTypes(binOp1.firstExp, x))
        case (None, None) => binOp1
      }
    }
    case uniOp: UniOp =>
      val inputSize = if (UniOperator.changesSize(uniOp.operator)) None else size
      uniOp.copy(exp = inferConstantTypes(uniOp.exp, inputSize))
    case lit: Literal if (lit.size == None) => lit.copy(size = size)
    case _ => expr
  }

  // TODO this is a temporary rudimentary analysis that should be replaced with a static analysis method later
  // TODO implement this
  private def regionAnalysis(): Unit = flowGraph.getFunctions.forEach(f => f.getBlocks.forEach(b =>
      b.setLines(b.getLines.asScala.map(regionAnalysis).asJava)
    ))

  // private def isOnStack()

  private def regionAnalysis(stmt: Stmt): Stmt = stmt match {
    // case MemLoad(BinOp(_, v: Var, _), _) if (v.name == "SP") => stmt
    case _: MemAssign => stmt
    case x => x
  }

  private def writeToFile(): Unit = {
    try {
      val writer = new BufferedWriter(new FileWriter(outputFileName, false))
      writer.write(flowGraph.toString)
      writer.flush()
    } catch {
      case _: IOException => System.err.println("Error writing to file.")
    }
  }

  private def uniqueVarName: String = return "p" + uniqueNum

  private def uniqueLabel: String = return "l" + uniqueNum

  private def uniqueNum: Int = {
    uniqueInt += 1
    uniqueInt
  }

}
