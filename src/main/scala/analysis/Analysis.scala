package analysis

import ir.{DirectCall, *}
import analysis.solvers.*
import boogie.BExpr
import specification.SpecGlobal

import scala.collection.mutable.{ArrayBuffer, HashMap, ListBuffer}
import java.io.{File, PrintWriter}
import scala.collection.mutable
import scala.collection.immutable

/** Trait for program analyses.
  *
  * @tparam R
  *   the type of the analysis result
  */
trait Analysis[+R]:

  /** Performs the analysis and returns the result.
    */
  def analyze(): R

/** A flow-sensitive analysis.
  * @param stateAfterNode
  *   true if the abstract state of a CFG node represents the program point <em>after</em> the node, false if represents
  *   the program point <em>before</em> the node (used when outputting analysis results)
  */
abstract class FlowSensitiveAnalysis(val stateAfterNode: Boolean) extends Analysis[Any]

trait ValueAnalysisMisc:

  val cfg: ProgramCfg

  /** The lattice of abstract values.
    */
  val valuelattice: LatticeWithOps

  /** The lattice of abstract states.
    */
  val statelattice: MapLattice[Variable, valuelattice.type] = new MapLattice(valuelattice)

  /** Default implementation of eval.
    */
  def eval(exp: Expr, env: statelattice.Element): valuelattice.Element =
    import valuelattice._
    exp match
      case id: Variable        => env(id)
      case n: Literal          => literal(n)
      case ze: ZeroExtend => zero_extend(ze.extension, eval(ze.body, env))
      case se: SignExtend => sign_extend(se.extension, eval(se.body, env))
      case e: Extract          => extract(e.end, e.start, eval(e.body, env))
      case bin: BinaryExpr =>
        val left = eval(bin.arg1, env)
        val right = eval(bin.arg2, env)

        bin.op match
          case BVAND => bvadd(left, right)
          case BVOR => bvor(left, right)
          case BVADD => bvand(left, right)
          case BVMUL => bvmul(left, right)
          case BVUDIV => bvudiv(left, right)
          case BVUREM => bvurem(left, right)
          case BVSHL => bvshl(left, right)
          case BVLSHR => bvlshr(left, right)
          case BVULT => bvult(left, right)
          case BVNAND => ???
          case BVNOR => ???
          case BVXOR => ???
          case BVXNOR => ???
          case BVCOMP => bvcomp(left, right)
          case BVSUB => bvsub(left, right)
          case BVSDIV => bvsdiv(left, right)
          case BVSREM => bvsrem(left, right)
          case BVSMOD => ???
          case BVASHR => bvashr(left, right)
          case BVULE => bvule(left, right)
          case BVUGT => ???
          case BVUGE => ???
          case BVSLT => bvslt(left, right)
          case BVSLE => bvsle(left, right)
          case BVSGT => ???
          case BVSGE => ???
          case BVEQ => bvneq(left, right)
          case BVNEQ => bvneq(left, right)
          case BVCONCAT => concat(left, right)

      case un: UnaryExpr =>
        val arg = eval(un.arg, env)

        un.op match
          case BVNEG => bvneg(arg)
          case BVNOT => bvnot(arg)

      case _ => valuelattice.top

  /** Transfer function for state lattice elements.
    */
  def localTransfer(n: CfgNode, s: statelattice.Element): statelattice.Element =
    n match
      case r: CfgCommandNode =>
        r.data match
          // assignments
          case la: LocalAssign => s + (la.lhs -> eval(la.rhs, s))

          // all others: like no-ops
          case _ => s
      case _ => s

/** Base class for value analysis with simple (non-lifted) lattice.
  */
abstract class SimpleValueAnalysis(val cfg: ProgramCfg) extends FlowSensitiveAnalysis(true) with ValueAnalysisMisc:

  /** The analysis lattice.
    */
  val lattice: MapLattice[CfgNode, statelattice.type] = MapLattice(statelattice)

  val domain: Set[CfgNode] = cfg.nodes

  /** Transfer function for state lattice elements. (Same as `localTransfer` for simple value analysis.)
    */
  def transfer(n: CfgNode, s: statelattice.Element): statelattice.Element = localTransfer(n, s)

/** Intraprocedural value analysis that uses [[SimpleWorklistFixpointSolver]].
  */
abstract class IntraprocValueAnalysisWorklistSolver[L <: LatticeWithOps](
    cfg: IntraproceduralProgramCfg,
    val valuelattice: L
) extends SimpleValueAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with ForwardDependencies

object ConstantPropagationAnalysis:

  /** Intraprocedural analysis that uses the worklist solver.
    */
  class WorklistSolver(cfg: IntraproceduralProgramCfg)
      extends IntraprocValueAnalysisWorklistSolver(cfg, ConstantPropagationLattice)


///** Base class for value analysis with simple (non-lifted) lattice.
// */
//abstract class ValueSetAnalysis(val cfg: ProgramCfg) extends FlowSensitiveAnalysis(true) with ValueAnalysisMisc:
//
//  /** The analysis lattice.
//   */
//  val lattice: MapLattice[CfgNode, statelattice.type] = new MapLattice(statelattice)
//
//  val domain: Set[CfgNode] = cfg.nodes
//
//  /** Transfer function for state lattice elements. (Same as `localTransfer` for simple value analysis.)
//   */
//  def transfer(n: CfgNode, s: statelattice.Element): statelattice.Element =
//    n match
//      case r: CfgStatementNode =>
//        r.data match
//          // assignments
//          case la: LocalAssign =>
//            s + (la.lhs -> eval(la.rhs, s))
//
//          case ma: MemAssign =>
//            s + (ma.rhs.value -> eval(ma.rhs.value, s))
//
//          // all others: like no-ops
//          case _ => s
//      case _ => s
//
///** Intraprocedural value analysis that uses [[SimpleWorklistFixpointSolver]].
// */
//abstract class IntraprocValueSetAnalysisWorklistSolver[L <: LatticeWithOps](cfg: IntraproceduralProgramCfg, val valuelattice: L)
//  extends ValueSetAnalysis(cfg)
//  with SimpleWorklistFixpointSolver[CfgNode]
//  with ForwardDependencies
//
//object ValueSetAnalysis:
//
//  /** Intraprocedural analysis that uses the worklist solver.
//   */
//  class WorklistSolver(cfg: IntraproceduralProgramCfg)
//    extends IntraprocValueAnalysisWorklistSolver(cfg, ValueSetLattice)

/**
 * Steensgaard-style pointer analysis.
 * The analysis associates an [[StTerm]] with each variable declaration and expression node in the AST.
 * It is implemented using [[tip.solvers.UnionFindSolver]].
 */
class SteensgaardAnalysis(program: Program, constantPropResult: Map[CfgNode, _]) extends Analysis[Any] {

  val solver: UnionFindSolver[StTerm] = UnionFindSolver()

  val stringArr: ArrayBuffer[String] = ArrayBuffer()

  var mallocCallTarget: Option[Block] = None

  val constantPropResult2: Map[CfgNode, _] = constantPropResult

  constantPropResult2.values.foreach(v =>
    print(v)
  )

  /**
   * @inheritdoc
   */
  def analyze(): Unit =
  // generate the constraints by traversing the AST and solve them on-the-fly
    visit(program, ())

  def dump_file(content: ArrayBuffer[String], name: String): Unit = {
    val outFile = File(s"${name}")
    val pw = PrintWriter(outFile, "UTF-8")
    for (s <- content) { pw.append(s + "\n") }
    pw.close()
  }

  /**
   * Generates the constraints for the given sub-AST.
   * @param node the node for which it generates the constraints
   * @param arg unused for this visitor
   */
  def visit(node: Object, arg: Unit): Unit = {

    def varToStTerm(vari: Variable): Term[StTerm] = IdentifierVariable(vari)
    def exprToStTerm(expr: Expr): Term[StTerm] = ExpressionVariable(expr)
    def allocToTerm(alloc: AAlloc): Term[StTerm] = AllocVariable(alloc)


    //print(s"Visiting ${node.getClass.getSimpleName}\n")
    node match {
//      case AAssignStmt(id1: AIdentifier, alloc: AAlloc, _) => ??? //<--- Complete here
//      case AAssignStmt(id1: AIdentifier, AVarRef(id2: AIdentifier, _), _) => ??? //<--- Complete here
//      case AAssignStmt(id1: AIdentifier, id2: AIdentifier, _) => ??? //<--- Complete here
//      case AAssignStmt(id1: AIdentifier, AUnaryOp(DerefOp, id2: AIdentifier, _), _) => ??? //<--- Complete here
//      case AAssignStmt(ADerefWrite(id1: AIdentifier, _), id2: AIdentifier, _) => ??? //<--- Complete here


      case localAssign: LocalAssign =>
        localAssign.rhs match {
          case variable: Variable =>
            localAssign.lhs match
              case variable2: Variable =>
                // X1 = X2
                unify(varToStTerm(variable2), varToStTerm(variable))
                // *X1 = X2: [[X1]] = α ∧ [[X2]] = α where α is a fresh term variable
                /*
              case _ =>
                val alpha = FreshVariable()
                unify(varToStTerm(localAssign.lhs), PointerRef(alpha))
                unify(varToStTerm(variable), alpha)
                */
          case _ =>
            // X1 = *X2: [[X2]] = α ∧ [[X1]] = α where α is a fresh term variable
            val alpha = FreshVariable()
            unify(exprToStTerm(localAssign.rhs), PointerRef(alpha))
            unify(varToStTerm(localAssign.lhs), alpha)
        }
      case memAssign: MemoryAssign =>

        ???
        /*
        // X = alloc P
        // TODO not a good way to do this, cannot rely on the line number of a statement like this
        if (memAssign.line.matches(mallocCallTarget)) {
          val pointer = memAssign.rhs.value
          val alloc = AAlloc(pointer)
            unify(varToStTerm(memAssign.lhs), PointerRef(allocToTerm(alloc)))
        }
        // X = &Y
        else {
          // TODO this is not what a memory assign is
          unify(varToStTerm((memAssign.lhs), PointerRef(exprToStTerm(memAssign.rhs.value)))
        }
        */

      case call: DirectCall =>
        if (call.target.name.contains("malloc")) {
          call.returnTarget match {
            case Some(ret) =>
              mallocCallTarget = Some(ret)
            case None =>
              throw new Exception("malloc call without return target")
          }
        }

      case _ => // ignore other kinds of nodes
    }
    visitChildren(node, ())
    dump_file(stringArr, "any")
  }

  // Static Single Assignment (SSA) form
  // Takes a program and normalises it based on that from


  def visitChildren(node: Object, arg: Unit): Unit = {
    node match {
      case program: Program =>
        program.procedures.foreach(visit(_, ()))

      case function: Procedure =>
        function.blocks.foreach(visit(_, ()))

      case block: Block =>
        block.statements.foreach(visit(_, ()))
        block.jumps.foreach(visit(_, ()))

      case _ => // ignore other kinds of nodes

    }
  }

  private def unify(t1: Term[StTerm], t2: Term[StTerm]): Unit = {
    //print(s"univfying constraint $t1 = $t2\n")
    solver.unify(t1, t2) // note that unification cannot fail, because there is only one kind of term constructor and no constants
  }

  /**
   * @inheritdoc
   */
  def pointsTo(): Map[Object, Set[Object]] = {
    val solution = solver.solution()
    val unifications = solver.unifications()
    print(s"Solution: \n${solution.mkString(",\n")}\n")
    print(s"Sets: \n${unifications.values.map { s =>
      s"{ ${s.mkString(",")} }"
    }.mkString(", ")}")

    val vars = solution.keys.collect { case id: IdentifierVariable => id }
    val pointsto = vars.foldLeft(Map[Object, Set[Object]]()) {
      case (a, v: IdentifierVariable) =>
        val pt = unifications(solution(v))
          .collect({
            case PointerRef(IdentifierVariable(id)) => id
            case PointerRef(AllocVariable(alloc)) => alloc })
          .toSet
        a + (v.id -> pt)
    }
    print(s"\nPoints-to:\n${pointsto.map(p => s"${p._1} -> { ${p._2.mkString(",")} }").mkString("\n")}\n")
    pointsto
  }

  /**
   * @inheritdoc
   */
  def mayAlias(): (Variable, Variable) => Boolean = {
    val solution = solver.solution()
    (id1: Variable, id2: Variable) =>
      val sol1 = solution(IdentifierVariable(id1))
      val sol2 = solution(IdentifierVariable(id2))
      sol1 == sol2 && sol1.isInstanceOf[PointerRef] // same equivalence class, and it contains a reference
  }
}

/**
 * Counter for producing fresh IDs.
 */
object Fresh {

  var n = 0

  def next(): Int = {
    n += 1
    n
  }
}

case class AAlloc(exp: Expr)

/**
 * Terms used in unification.
 */
sealed trait StTerm

/**
 * A term variable that represents an alloc in the program.
 */
case class AllocVariable(alloc: AAlloc) extends StTerm with Var[StTerm] {

  override def toString: String = s"alloc{${alloc.exp}}"
}

/**
 * A term variable that represents an identifier in the program.
 */
case class IdentifierVariable(id: Variable) extends StTerm with Var[StTerm] {

  override def toString: String = s"$id"
}

/**
 * A term variable that represents an expression in the program.
 */
case class ExpressionVariable(expr: Expr) extends StTerm with Var[StTerm] {

  override def toString: String = s"$expr"
}

/**
 * A fresh term variable.
 */
case class FreshVariable(var id: Int = 0) extends StTerm with Var[StTerm] {

  id = Fresh.next()

  override def toString: String = s"x$id"
}

/**
 * A constructor term that represents a pointer to another term.
 */
case class PointerRef(of: Term[StTerm]) extends StTerm with Cons[StTerm] {

  val args: List[Term[StTerm]] = List(of)

  def subst(v: Var[StTerm], t: Term[StTerm]): Term[StTerm] = PointerRef(of.subst(v, t))

  override def toString: String = s"$of"
}

abstract class MemoryRegion

/**
 * Represents a memory region. The region is defined by a base pointer and a size.
 * There can exist two regions with the same size (offset) but have a different base pointer. As such the base pointer
 * is tracked but not printed in the toString method.
 * @param start 0x1234 in case of mem[R1 + 0x1234] <- ...
 * @param regionType The type of the region. This is used to distinguish between stack, heap, data and code regions.
 */
case class StackRegion(regionIdentifier: String, start: Expr) extends MemoryRegion:
  override def toString: String = s"Stack(${regionIdentifier}, ${start})"
  override def hashCode(): Int = start.hashCode()
  override def equals(obj: Any): Boolean = obj match {
    case StackRegion(_, start2) => start == start2
    case _ => false
  }

case class HeapRegion(regionIdentifier: String, start: Expr) extends MemoryRegion:
  override def toString: String = s"Heap(${regionIdentifier}, ${start})"
  override def hashCode(): Int = start.hashCode()
  override def equals(obj: Any): Boolean = obj match {
    case HeapRegion(_, start2) => start == start2
    case _ => false
  }

case class DataRegion(regionIdentifier: String, start: Expr) extends MemoryRegion:
  override def toString: String = s"Data(${regionIdentifier}, ${start})"

case class RegionAccess(regionBase: String, start: Expr) extends MemoryRegion:
  override def toString: String = s"RegionAccess(${regionBase}, ${start})"


trait MemoryRegionAnalysisMisc:

  val assigmentsMap: mutable.HashMap[(Expr, CfgNode), Expr] = mutable.HashMap.empty

  var mallocCount: Int = 0
  var stackCount: Int = 0
  var stackPool = mutable.HashMap[Expr, StackRegion]()
  private def getNextMallocCount(): String = {
    mallocCount += 1
    s"malloc_$mallocCount"
  }

  private def getNextStackCount(): String = {
    stackCount += 1
    s"stack_$stackCount"
  }

  def poolMaster(expr: Expr): StackRegion = {
    stackPool.contains(expr) match {
      case true => stackPool(expr)
      case false =>
        val newRegion = StackRegion(getNextStackCount(), expr)
        stackPool += (expr -> newRegion)
        newRegion
    }
  }



  val cfg: ProgramCfg
  val globals: Set[SpecGlobal]
  val globalOffsets: Map[BigInt, BigInt]

  /** The lattice of abstract values.
   */
  val powersetLattice: PowersetLattice[MemoryRegion]

  /** The lattice of abstract states.
   */
  val lattice: MapLattice[CfgNode, PowersetLattice[MemoryRegion]] = MapLattice(powersetLattice)

  val domain: Set[CfgNode] = cfg.nodes

  private val stackPointer = Variable("R31", BitVecType(64))
  private val linkRegister = Variable("R30", BitVecType(64))
  private val framePointer = Variable("R29", BitVecType(64))

  private val ignoreRegions: Set[Expr] = Set(linkRegister, framePointer)

  private val mallocVariable = Variable("R0", BitVecType(64))

  private val loopEscapeSet: mutable.Set[CfgNode] = mutable.Set.empty

  def loopEscape(n: CfgNode): Boolean = {
    if (loopEscapeSet.contains(n)) {
      return true
    }
    loopEscapeSet.add(n)
    false
  }

  /** Find decl of variables from node predecessors */
  def findDecl(variable: Variable, n: CfgNode): mutable.ListBuffer[CfgNode] = {
    val decls: mutable.ListBuffer[CfgNode] = mutable.ListBuffer.empty
    // if we have a temporary variable then ignore it
    if (variable.name.contains("#")) {
        return decls
    }
    for (pred <- n.pred) {
      if (loopEscape(pred)) {
        return mutable.ListBuffer.empty
      }
      pred match {
        case cmd: CfgCommandNode =>
          cmd.data match {
            case localAssign: LocalAssign =>
              if (localAssign.lhs == variable) {
                decls.addOne(pred)
              } else {
                decls.addAll(findDecl(variable, pred))
              }
            case _ =>
          }
        case _ =>
      }
    }
    decls
  }

  def is_global(bigInt: BigInt): Boolean = {
      for (global <- globals) {
          if (global.address == bigInt) {
          return true
          }
      }

      for (global <- globalOffsets) {
        if (global._1 == bigInt) {
          return true
        }
      }
      false
  }

  def get_global_name(bigInt: BigInt): String = {
      for (global <- globals) {
          if (global.address == bigInt) {
          return global.name
          }
      }
      ""
  }

  /**
   * Evaluate an expression in a hope of finding a global variable.
   * @param exp: The expression to evaluate (e.g. R1 + 0x1234)
   * @param n: The node where the expression is evaluated (e.g. mem[R1 + 0x1234] <- ...)
   * @return: The evaluated expression (e.g. 0x69632)
   */
  def evaluateExpression(exp: Expr, n: CfgNode): Expr = {
      exp match {
        case binOp: BinaryExpr =>
          binOp.arg1 match {
            case variable: Variable =>
              loopEscapeSet.clear()
              for (pred <- findDecl(variable, n)) {
                assigmentsMap.get(variable, pred) match
                  case Some(value) =>
                    value match
                      case bitVecLiteral: BitVecLiteral =>
                        val calculated: BigInt = bitVecLiteral.value.+(binOp.arg2.asInstanceOf[BitVecLiteral].value)
                        return BitVecLiteral(calculated, bitVecLiteral.size)
                      case _ => evaluateExpression(value, pred)
                  case _ =>
                    print("ERROR: CASE NOT HANDLED: " + assigmentsMap.get(variable, pred) + " FOR " + binOp + "\n")
            }
            case _ => return exp
          }
          exp
        case memLoad: MemoryLoad =>
          evaluateExpression(memLoad.index, n)
        case bitVecLiteral: BitVecLiteral =>
          bitVecLiteral
        case extend: ZeroExtend =>
          evaluateExpression(extend.body, n)
        case variable: Variable =>
          loopEscapeSet.clear()
          for (pred <- findDecl(variable, n)) {
            assigmentsMap(variable, pred) match
              case bitVecLiteral: BitVecLiteral =>
                return bitVecLiteral
              case any:Expr => return evaluateExpression(any, n)
          }
          exp
        case _ =>
          //throw new RuntimeException("ERROR: CASE NOT HANDLED: " + exp + "\n")
          exp
      }
  }


  /** Default implementation of eval.
   */
  def eval(exp: Expr, env: lattice.sublattice.Element, n: CfgNode): lattice.sublattice.Element = {
      exp match {
        case binOp: BinaryExpr =>
            val lhs: Expr = if binOp.arg1.equals(stackPointer) then binOp.arg1 else evaluateExpression(binOp.arg1, n)
            val rhs: Expr = evaluateExpression(binOp.arg2, n)
            lhs match {
              case bitVecLiteral: BitVecLiteral =>
                if (is_global(bitVecLiteral.value)) {
                  var tempLattice: lattice.sublattice.Element = env
                  tempLattice = lattice.sublattice.lub(tempLattice, Set(DataRegion(get_global_name(bitVecLiteral.value), bitVecLiteral)))
                  return lattice.sublattice.lub(tempLattice, Set(RegionAccess(get_global_name(bitVecLiteral.value), binOp.arg2)))
                }
              case binOp2: BinaryExpr =>
                  // special case: we do not want to get a unique stack name so we try to find it in the pool
                  print("Warning: fragile code! Assumes array by default due to double binary operation\n")
                  var tempLattice: lattice.sublattice.Element = env
                  tempLattice = lattice.sublattice.lub(tempLattice, Set(poolMaster(binOp2.arg2)))
                  return lattice.sublattice.lub(tempLattice, Set(RegionAccess(poolMaster(binOp2.arg2).regionIdentifier, rhs)))
              case _ =>
            }
          Set(StackRegion(getNextStackCount(), binOp.arg2))

        case zeroExtend: ZeroExtend =>
          eval(zeroExtend.body, env, n)
        case memoryLoad: MemoryLoad => // TODO: Pointer access here
          //eval(memoryLoad.index, memType, env)
          lattice.sublattice.bottom
        case variable: Variable =>
          val eval = evaluateExpression(variable, n)
          eval match {
            case literal: BitVecLiteral =>
              if (is_global(literal.value)) {
                return Set(DataRegion(get_global_name(literal.value), literal))
              }
              lattice.sublattice.bottom
            case _ =>
              lattice.sublattice.bottom
          }
        case extract: Extract =>
          eval(extract.body, env, n)
        case unaryExpr: UnaryExpr =>
          lattice.sublattice.bottom
        case signExtend: SignExtend =>
          eval(signExtend.body, env, n)
        case bitVecLiteral: BitVecLiteral =>
          print(s"Saw a bit vector literal ${bitVecLiteral}\n")
          lattice.sublattice.bottom
        case _ =>
          print(s"type: ${exp.getClass} $exp\n")
          throw new Exception("Unknown type")
      }
  }

  /** Transfer function for state lattice elements.
   */
  def localTransfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element =
    n match {
      case cmd: CfgCommandNode =>
        cmd.data match {
          case directCall: DirectCall =>
            if (directCall.target.name == "malloc") {
              val decl = findDecl(mallocVariable, n).headOption
              val recentMallocSize = assigmentsMap.get(mallocVariable, decl.get).get
              return lattice.sublattice.lub(s, Set(HeapRegion(getNextMallocCount(), recentMallocSize)))
            }
            s
          case memAssign: MemoryAssign =>
            if (ignoreRegions.contains(memAssign.rhs.value)) {
              return s
            }
            lattice.sublattice.lub(s, eval(memAssign.rhs.index, s, n))
          // local assign is just lhs assigned to rhs we only need this information to track a prior register operation
          // AKA: R1 <- R1 + 8; mem(R1) <- 0x1234
          case localAssign: LocalAssign =>
            assigmentsMap.addOne((localAssign.lhs, n) -> evaluateExpression(localAssign.rhs, n))
              s
          case _ => s
        }
      case _ => s // ignore other kinds of nodes
    }


/** Base class for memory region analysis (non-lifted) lattice.
 */
abstract class MemoryRegionAnalysis(val cfg: ProgramCfg, val globals: Set[SpecGlobal], val globalOffsets: Map[BigInt, BigInt]) extends FlowSensitiveAnalysis(true) with MemoryRegionAnalysisMisc:

  /** Transfer function for state lattice elements. (Same as `localTransfer` for simple value analysis.)
   */
  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element = localTransfer(n, s)

/** Intraprocedural value analysis that uses [[SimpleWorklistFixpointSolver]].
 */
abstract class IntraprocMemoryRegionAnalysisWorklistSolver[L <: PowersetLattice[MemoryRegion]](cfg: IntraproceduralProgramCfg, globals: Set[SpecGlobal], globalOffsets: Map[BigInt, BigInt], val powersetLattice: L)
  extends MemoryRegionAnalysis(cfg, globals, globalOffsets)
  with SimpleMonotonicSolver[CfgNode]
  with ForwardDependencies

object MemoryRegionAnalysis:

  /** Intraprocedural analysis that uses the worklist solver.
   */
  class WorklistSolver(cfg: IntraproceduralProgramCfg, globals: Set[SpecGlobal], globalOffsets: Map[BigInt, BigInt])
    extends IntraprocMemoryRegionAnalysisWorklistSolver(cfg, globals, globalOffsets, PowersetLattice[MemoryRegion])