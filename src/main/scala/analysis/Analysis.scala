package analysis

import ir.*
import analysis.solvers.*

import scala.collection.mutable.{ArrayBuffer, HashMap, ListBuffer}
import java.io.{File, PrintWriter}
import scala.collection.mutable
import scala.collection.immutable
import util.Logger

/** Trait for program analyses.
  *
  * @tparam R
  *   the type of the analysis result
  */
trait Analysis[+R]:

  /** Performs the analysis and returns the result.
    */
  def analyze(intra: Boolean): R

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
      case id: Variable   => env(id)
      case n: Literal     => literal(n)
      case ze: ZeroExtend => zero_extend(ze.extension, eval(ze.body, env))
      case se: SignExtend => sign_extend(se.extension, eval(se.body, env))
      case e: Extract     => extract(e.end, e.start, eval(e.body, env))
      case bin: BinaryExpr =>
        val left = eval(bin.arg1, env)
        val right = eval(bin.arg2, env)
        bin.op match
          case BVADD  => bvadd(left, right)
          case BVSUB  => bvsub(left, right)
          case BVMUL  => bvmul(left, right)
          case BVUDIV => bvudiv(left, right)
          case BVSDIV => bvsdiv(left, right)
          case BVSREM => bvsrem(left, right)
          case BVUREM => bvurem(left, right)
          case BVSMOD => bvsmod(left, right)
          case BVAND  => bvand(left, right)
          case BVOR   => bvor(left, right)
          case BVXOR  => bvxor(left, right)
          case BVNAND => bvnand(left, right)
          case BVNOR  => bvnor(left, right)
          case BVXNOR => bvxnor(left, right)
          case BVSHL  => bvshl(left, right)
          case BVLSHR => bvlshr(left, right)
          case BVASHR => bvashr(left, right)
          case BVCOMP => bvcomp(left, right)

          case BVULE => bvule(left, right)
          case BVUGE => bvuge(left, right)
          case BVULT => bvult(left, right)
          case BVUGT => bvugt(left, right)

          case BVSLE => bvsle(left, right)
          case BVSGE => bvsge(left, right)
          case BVSLT => bvslt(left, right)
          case BVSGT => bvsgt(left, right)

          case BVCONCAT => concat(left, right)
          case BVNEQ    => bvneq(left, right)
          case BVEQ     => bveq(left, right)

      case un: UnaryExpr =>
        val arg = eval(un.arg, env)

        un.op match
          case BVNOT => bvnot(arg)
          case BVNEG => bvneg(arg)

      case _ => valuelattice.top

  /** Transfer function for state lattice elements.
    */
  def localTransfer(n: CfgNode, s: statelattice.Element): statelattice.Element =
    n match
      case r: CfgCommandNode =>
        r.data match
          // assignments
          case la: LocalAssign =>
            s + (la.lhs -> eval(la.rhs, s))
          // all others: like no-ops
          case _ => s
      case _ => s

/** Base class for value analysis with simple (non-lifted) lattice.
  */
abstract class SimpleValueAnalysis(val cfg: ProgramCfg) extends FlowSensitiveAnalysis(true) with ValueAnalysisMisc:

  /** The analysis lattice.
    */
  val lattice: MapLattice[CfgNode, statelattice.type] = MapLattice(statelattice)

  /** Setup initial analysis domain with:
    *  - All function entry nodes with a priority, filtering out those without a body
    *  - All nodes that can't be trivially attributed to their predecessors (not part of a basic block)
    */
  val domain: Set[CfgNode] = cfg.nodes.toSet.collect{
    case n: CfgFunctionEntryNode if n.rpo != -1 => n
    case n: CfgNode if n.rpo != -1 && !n.trivial() => n
  }

  /** Transfer function for state lattice elements. (Same as `localTransfer` for simple value analysis.)
    */
  def transfer(n: CfgNode, s: statelattice.Element): statelattice.Element = localTransfer(n, s)

abstract class ValueAnalysisWorklistSolver[L <: LatticeWithOps](
    cfg: ProgramCfg,
    val valuelattice: L
) extends SimpleValueAnalysis(cfg)
    with ReversePostOrder
    with SimplePushDownWorklistFixpointSolver[CfgNode]
    with ForwardDependencies

object ConstantPropagationAnalysis:

  class WorklistSolver(cfg: ProgramCfg) extends ValueAnalysisWorklistSolver(cfg, ConstantPropagationLattice) {
    def analyzeAndUnpack(intra: Boolean) = super.analyze(intra).map(_.toMap)
  }



/** Counter for producing fresh IDs.
  */
object Fresh {

  var n = 0

  def next(): Int = {
    n += 1
    n
  }
}

trait MemoryRegion {
  val regionIdentifier: String
  var extent: Option[RangeKey] = None
}

class StackRegion(override val regionIdentifier: String, val start: BitVecLiteral) extends MemoryRegion {
  override def toString: String = s"Stack($regionIdentifier, $start)"
  override def hashCode(): Int = regionIdentifier.hashCode() * start.hashCode()
  override def equals(obj: Any): Boolean = obj match {
    case s: StackRegion => s.start == start && s.regionIdentifier == regionIdentifier
    case _ => false
  }
}

class HeapRegion(override val regionIdentifier: String) extends MemoryRegion {
  override def toString: String = s"Heap($regionIdentifier)"
  override def hashCode(): Int = regionIdentifier.hashCode()
  override def equals(obj: Any): Boolean = obj match {
    case h: HeapRegion => h.regionIdentifier == regionIdentifier
    case _ => false
  }
}

class DataRegion(override val regionIdentifier: String, val start: BitVecLiteral) extends MemoryRegion {
  override def toString: String = s"Data($regionIdentifier, $start)"
  override def hashCode(): Int = regionIdentifier.hashCode() * start.hashCode()
  override def equals(obj: Any): Boolean = obj match {
    case d: DataRegion => d.start == start && d.regionIdentifier == regionIdentifier
    case _ => false
  }
}

trait MemoryRegionAnalysisMisc:

  var mallocCount: Int = 0
  var stackCount: Int = 0
  val stackMap: mutable.Map[CfgFunctionEntryNode, mutable.Map[Expr, StackRegion]] = mutable.HashMap()
  private def nextMallocCount() = {
    mallocCount += 1
    s"malloc_$mallocCount"
  }

  private def nextStackCount() = {
    stackCount += 1
    s"stack_$stackCount"
  }

  /**
   * Controls the pool of stack regions. Each pool is unique to a function.
   * If the offset has already been defined in the context of the function, then the same region is returned.
   * @param expr: the offset
   * @param parent: the function entry node
   * @return the stack region corresponding to the offset
   */
  def poolMaster(expr: BitVecLiteral, parent: CfgFunctionEntryNode): StackRegion = {
    val stackPool = stackMap.getOrElseUpdate(parent, mutable.HashMap())
    if (stackPool.contains(expr)) {
      stackPool(expr)
    } else {
      val newRegion = StackRegion(nextStackCount(), expr)
      stackPool += (expr -> newRegion)
      newRegion
    }
  }

  def unwrapExpr(expr: Expr) : ListBuffer[Expr] = {
    val buffers = ListBuffer[Expr]()
    expr match {
      case e: Extract => unwrapExpr(e.body)
      case e: SignExtend => unwrapExpr(e.body)
      case e: ZeroExtend => unwrapExpr(e.body)
      case repeat: Repeat => unwrapExpr(repeat.body)
      case unaryExpr: UnaryExpr => unwrapExpr(unaryExpr.arg)
      case binaryExpr: BinaryExpr =>
          unwrapExpr(binaryExpr.arg1)
          unwrapExpr(binaryExpr.arg2)
      case memoryLoad: MemoryLoad =>
        buffers.addOne(memoryLoad)
        unwrapExpr(memoryLoad.index)
      case _ =>
    }
    buffers
  }

  val cfg: ProgramCfg
  val globals: Map[BigInt, String]
  val globalOffsets: Map[BigInt, BigInt]
  val subroutines: Map[BigInt, String]
  val constantProp: Map[CfgNode, Map[Variable, ConstantPropagationLattice.Element]]

  /** The lattice of abstract values.
    */
  val powersetLattice: PowersetLattice[MemoryRegion]

  /** The lattice of abstract states.
    */
  val lattice: MapLattice[CfgNode, PowersetLattice[MemoryRegion]] = MapLattice(powersetLattice)

  val domain: Set[CfgNode] = cfg.nodes.toSet

  private val stackPointer = Register("R31", BitVecType(64))
  private val linkRegister = Register("R30", BitVecType(64))
  private val framePointer = Register("R29", BitVecType(64))

  private val ignoreRegions: Set[Expr] = Set(linkRegister, framePointer)

  private val mallocVariable = Register("R0", BitVecType(64))

  def eval(exp: Expr, env: lattice.sublattice.Element, n: CfgCommandNode): lattice.sublattice.Element = {
    Logger.debug(s"evaluating $exp")
    Logger.debug(s"env: $env")
    Logger.debug(s"n: $n")
    exp match {
      case binOp: BinaryExpr =>
        if (binOp.arg1 == stackPointer) {
          evaluateExpression(binOp.arg2, constantProp(n)) match {
            case Some(b: BitVecLiteral) => Set(poolMaster(b, n.parent))
            case None => env
          }
        } else {
          evaluateExpression(binOp, constantProp(n)) match {
            case Some(b: BitVecLiteral) => eval(b, env, n)
            case None => env
          }
        }
      case bitVecLiteral: BitVecLiteral =>
        if (globals.contains(bitVecLiteral.value)) {
          val globalName = globals(bitVecLiteral.value)
          Set(DataRegion(globalName, bitVecLiteral))
        } else if (subroutines.contains(bitVecLiteral.value)) {
          val subroutineName = subroutines(bitVecLiteral.value)
          Set(DataRegion(subroutineName, bitVecLiteral))
        } else if (globalOffsets.contains(bitVecLiteral.value)) {
          val val1 = globalOffsets(bitVecLiteral.value)
          if (subroutines.contains(val1)) {
            val globalName = subroutines(val1)
            Set(DataRegion(globalName, bitVecLiteral))
          } else {
            Set(DataRegion(s"Unknown_$bitVecLiteral", bitVecLiteral))
          }
        } else {
          //throw new Exception(s"Unknown type for $bitVecLiteral")
          // unknown region here
          Set(DataRegion(s"Unknown_$bitVecLiteral", bitVecLiteral))
        }
      case variable: Variable =>
        variable match {
          case _: LocalVar =>
            env
          case reg: Register if reg == stackPointer =>
            env
          case _ =>
            evaluateExpression(variable, constantProp(n)) match {
              case Some(b: BitVecLiteral) =>
                eval(b, env, n)
              case _ =>
                env // we cannot evaluate this to a concrete value, we need VSA for this
          }
        }
      case _ =>
        Logger.debug(s"type: ${exp.getClass} $exp\n")
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
              evaluateExpression(mallocVariable, constantProp(n)) match {
                case Some(b: BitVecLiteral) =>
                  lattice.sublattice.lub(s, Set(HeapRegion(nextMallocCount())))
                case None => s
              }
            } else {
              s
            }
          case memAssign: MemoryAssign =>
            if (ignoreRegions.contains(memAssign.rhs.value)) {
              return s
            }
            val result = eval(memAssign.rhs.index, s, cmd)
            /*
            don't modify the IR in the middle of the analysis like this, also this produces a lot of incorrect results
            result.collectFirst({
              case StackRegion(name, _, _, _) =>
                memAssign.rhs = MemoryStore(
                  Memory(name,
                    memAssign.rhs.mem.addressSize,
                    memAssign.rhs.mem.valueSize),
                  memAssign.rhs.index,
                  memAssign.rhs.value, memAssign.rhs.endian,
                  memAssign.rhs.size
                )
              case DataRegion(name, _, _, _) =>
                memAssign.rhs = MemoryStore(
                  Memory(name, memAssign.rhs.mem.addressSize, memAssign.rhs.mem.valueSize),
                  memAssign.rhs.index,
                  memAssign.rhs.value,
                  memAssign.rhs.endian,
                  memAssign.rhs.size
                )
              case _ =>
            })
            */
            lattice.sublattice.lub(s, result)
          case localAssign: LocalAssign =>
            var m = s
            unwrapExpr(localAssign.rhs).foreach {
              case memoryLoad: MemoryLoad =>
                val result = eval(memoryLoad.index, s, cmd)
                /*
                don't modify the IR in the middle of the analysis like this, this also produces incorrect results
                result.collectFirst({
                  case StackRegion(name, _, _, _) =>
                    memoryLoad.mem = Memory(name, memoryLoad.mem.addressSize, memoryLoad.mem.valueSize)
                  case DataRegion(name, _, _, _) =>
                    memoryLoad.mem = Memory(name, memoryLoad.mem.addressSize, memoryLoad.mem.valueSize)
                  case _ =>
                })
                */
                m = lattice.sublattice.lub(m, result)
              case _ => m
            }
            m
          case _ => s
        }
      case _ => s // ignore other kinds of nodes
    }

/** Base class for memory region analysis (non-lifted) lattice.
  */
abstract class MemoryRegionAnalysis(
    val cfg: ProgramCfg,
    val globals: Map[BigInt, String],
    val globalOffsets: Map[BigInt, BigInt],
    val subroutines: Map[BigInt, String],
    val constantProp: Map[CfgNode, Map[Variable, ConstantPropagationLattice.Element]]
) extends FlowSensitiveAnalysis(true)
    with MemoryRegionAnalysisMisc:

  /** Transfer function for state lattice elements. (Same as `localTransfer` for simple value analysis.)
    */
  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element = localTransfer(n, s)

abstract class IntraprocMemoryRegionAnalysisWorklistSolver[L <: PowersetLattice[MemoryRegion]](
    cfg: ProgramCfg,
    globals: Map[BigInt, String],
    globalOffsets: Map[BigInt, BigInt],
    subroutines: Map[BigInt, String],
    constantProp: Map[CfgNode, Map[Variable, ConstantPropagationLattice.Element]],
    val powersetLattice: L
) extends MemoryRegionAnalysis(cfg, globals, globalOffsets, subroutines, constantProp)
    with SimpleMonotonicSolver[CfgNode]
    with ForwardDependencies

object MemoryRegionAnalysis:

  class WorklistSolver(
      cfg: ProgramCfg,
      globals: Map[BigInt, String],
      globalOffsets: Map[BigInt, BigInt],
      subroutines: Map[BigInt, String],
      constantProp: Map[CfgNode, Map[Variable, ConstantPropagationLattice.Element]]
  ) extends IntraprocMemoryRegionAnalysisWorklistSolver(
        cfg,
        globals,
        globalOffsets,
        subroutines,
        constantProp,
        PowersetLattice[MemoryRegion]
  ) {
    def analyzeAndUnpack(intra: Boolean) = super.analyze(intra).toMap
  }
