package translating

import facts.exp.{Expr, Literal, MemExpr, Var}
import facts.stmt.Assign.{Assign, Load, Move, Store}
import facts.stmt.*
import facts.parameters.{InParameter, OutParameter}
import facts.{Fact, Label}
import translating.FlowGraph
import scala.collection.mutable.HashSet
import java.io.{BufferedWriter, FileWriter, IOException}
import java.util
import java.util.{ArrayList, HashMap, HashSet, LinkedList, List, Map, Objects, Set}
import scala.collection.mutable
import collection.JavaConverters.*

// TODO rewrite this file to make the flowGraph immutable (this should make whats happening a bit more transparent)
class BoogieTranslator(flowGraph: FlowGraph, outputFileName: String) {
  private var uniqueInt = 0;

  /** Starting point for a BIL translation.
    */
  def translate() = {
    createLabels()
    optimiseSkips()
    identifyImplicitParams()
    resolveInParams()
    resolveOutParams()
    resolveVars()
    addVarDeclarations()
    writeToFile()
  }

  private def createLabels(): Unit = {
    val lines = flowGraph.getViewOfLines
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
    case jmpStmt: JmpStmt => jmpStmt.getTarget
    case cjmpStmt: CJmpStmt => cjmpStmt.getTarget
    case _ => null
  }

  /** If a skip is not jumped to, we should remove it. Depends on:
    *   - {@link #createLabels ( )}
    */
  private def optimiseSkips(): Unit = {
    flowGraph.getViewOfLines.forEach(line => {
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
          case store: Store => store.getRhs match {
            case rhsVar: Var if (isRegister(rhsVar) && assignedRegisters.contains(rhsVar)) =>
              val param = new InParameter(new Var(uniqueVarName), rhsVar)
              param.setAlias(store.getLhs.asInstanceOf[MemExpr])
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
  private def removeDuplicateParamsAndMerge(params: util.List[InParameter]): Unit = {
    val iter = params.iterator
    while (iter.hasNext) {
      val param = iter.next
      params.forEach(otherParam => {
        if ((param ne otherParam) && param.getRegister == otherParam.getRegister) { // duplicate found
          if (param.getAlias == null) { // null alias => this is the explicit param
            otherParam.setName(param.getName)
          } else { // non-null alias => this is the implicit param
            otherParam.setAlias(param.getAlias)
          }
          iter.remove()
        }
      })
    }
  }

  /** Provides function calls with a list of the facts.parameters they will need to provide arguments for.
    */
  private def createCallArguments(func: EnterSub): Unit =
    getCallsToFunction(func).forEach(call =>
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
      val firstLines: List[Stmt] = function.getBlocks.get(0).getLines

      firstLines.forEach(line => {line match {
        case store: Store => (store.getRhs, store.getLhs) match {
          case (rhs: Var, lhs: MemExpr) =>
            for (param <- paramsWithAliases) {
              if (param.getAlias == lhs && param.getRegister == rhs)
                forRemoval.add(line)
            }
          case (_: Var, _) => ??? // We may need to handle this later
          case _ =>
        }
        case _ =>
      }})

      forRemoval.forEach(firstLines.remove)

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
      if (line.isInstanceOf[Load] || line.isInstanceOf[Move]) {
        val lhs = line.asInstanceOf[Assign].getLhs.asInstanceOf[Var]
        // TODO slow
        if (
          flowGraph.getGlobalInits.stream.noneMatch(init => init.getVariable.getName == lhs.getName)
          && function.getHeader.getInParams.stream.noneMatch((inParam) => inParam.getName.getName == lhs.getName) // TODO check if this is needed
          && !(function.getHeader.getOutParam.getName.getName == lhs.getName)
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
  private def addVarDeclarations(): Unit = {
    flowGraph.getFunctions.forEach(function =>
      for (localVar <- getLocalVarsInFunction(function)) {
        // TODO i think this could be replaced by a none label as well
        function.addInitStmt(new InitStmt(localVar, uniqueLabel))
      }
    )
  }

  // TODO not sure if we need this (could we rewrite createCallAgument)
  private def getCallsToFunction(function: EnterSub): List[CallStmt] = {
    flowGraph.getViewOfLines.asScala.filter(line => line match {
      case callStmt: CallStmt if (callStmt.getFuncName == function.getFuncName) => true
      case _ => false
    }).asJava.asInstanceOf[List[CallStmt]]
  }

  private def isRegister(varFact: Var): Boolean = varFact.getName.charAt(0) == 'X'

  /** Resolves outParams by crudely replacing all references to their associated register with their human-readable
    * name.
    */
  private def resolveOutParams(): Unit =
    flowGraph.getFunctions.forEach(function =>
      val outParam: OutParameter = function.getHeader.getOutParam
      // TODO check will not be necassary if outparam is a scala class
      if (outParam != null)
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
      function.getBlocks.forEach(block => constantPropagation(block.getLines))
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
  private def constantPropagation(lines: List[Stmt]): Unit = { // these mapped ExpFacts are expected to only contain literals
    val values = new HashMap[Var, Literal]
    // assignments that will be removed if the lhs variable is re-assigned later
    val pendingRemoval = new HashMap[Var, Assign]
    // list of lines that will be removed once the loop exits
    val toRemove = new ArrayList[Assign]
    lines.forEach(line => {
        // with the exception of the lhs of assignments, replace any instances of variables with their mapped values
        // note that we don't make an exception for store assignments because their lhs is always a memFact, not var
        line match {
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
          case _ => values.forEach((variable: Var, literal: Literal) => replaceAllMatchingChildren(line, variable, literal))
        }
      }
    )
    toRemove.forEach(lines.remove)
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
