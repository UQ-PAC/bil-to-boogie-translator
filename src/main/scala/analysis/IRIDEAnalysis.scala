package analysis

import ir.{Block, CFGPosition, Command, DirectCall, Procedure, Program}

/**
 * Base trait for IDE analyses.
 * @tparam D the type of items
 * @tparam L the type of the value lattice
 * Adapted from Tip
 * https://github.com/cs-au-dk/TIP/blob/master/src/tip/solvers/IDEAnalysis.scala
 * The special item representing the empty element in IDE.
 */
final case class Lambda()

trait IRIDEAnalysis[E, EE, C, R, D, T, L <: Lattice[T]] {
  val program: Program

  type DL = Either[D, Lambda]

  /**
   * The value lattice.
   */
  val valuelattice: L

  /**
   * The edge lattice.
   */
  val edgelattice: EdgeFunctionLattice[T, valuelattice.type]

  /**
   * Edges for call-to-entry.
   */
  def edgesCallToEntry(call: C, entry: E)(d: DL): Map[DL, edgelattice.Element]

  /**
   * Edges for exit-to-aftercall.
   */
  def edgesExitToAfterCall(exit: EE, aftercall: R)(d: DL): Map[DL, edgelattice.Element]

  /**
   * Edges for call-to-aftercall.
   */
  def edgesCallToAfterCall(call: C, aftercall: R)(d: DL): Map[DL, edgelattice.Element]

  /**
   * Edges for other CFG nodes.
   */
  def edgesOther(n: CFGPosition)(d: DL): Map[DL, edgelattice.Element]
}


trait ForwardIDEAnalysis[D, T, L <: Lattice[T]] extends IRIDEAnalysis[Procedure, Command, DirectCall, Block, D, T, L]


trait BackwardIDEAnalysis[D, T, L <: Lattice[T]] extends IRIDEAnalysis[Command, Procedure, Block, DirectCall, D, T, L]
