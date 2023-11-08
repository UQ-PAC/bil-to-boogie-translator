package analysis.solvers

import analysis._
import scala.collection.immutable.ListSet
import scala.collection.mutable.LinkedHashSet
import scala.collection.mutable.PriorityQueue

/** Base trait for lattice solvers.
  */
trait LatticeSolver:

  /** The lattice used by the solver.
    */
  val lattice: Lattice

  /** The analyze function.
    */
  def analyze(intra: Boolean): lattice.Element

/** Base trait for map lattice solvers.
  * @tparam N
  *   type of the elements in the map domain.
  */
trait MapLatticeSolver[N] extends LatticeSolver with Dependencies[N]:

  /** Must be a map lattice.
    */
  val lattice: MapLattice[N, Lattice]

  /** The transfer function.
    */
  def transfer(n: N, s: lattice.sublattice.Element): lattice.sublattice.Element

  /** The constraint function for individual elements in the map domain. First computes the join of the incoming
    * elements and then applies the transfer function.
    * @param n
    *   the current location in the map domain
    * @param x
    *   the current lattice element for all locations
    * @param intra
    *   true if the cfg is treated as intraprocedural, else interprocedural
    * @return
    *   the output sublattice element
    */
  def funsub(n: N, x: lattice.Element, intra: Boolean): lattice.sublattice.Element =
    transfer(n, join(n, x, intra))

  /** Computes the least upper bound of the incoming elements.
    */
  def join(n: N, o: lattice.Element, intra: Boolean): lattice.sublattice.Element =
    val states = indep(n, intra).map(o(_))
    states.foldLeft(lattice.sublattice.bottom)((acc, pred) => lattice.sublattice.lub(acc, pred))

/** An abstract worklist algorithm.
  *
  * @tparam N
  *   type of the elements in the worklist.
  */
trait Worklist[N]:

  /** Called by [[run]] to process an item from the worklist.
    */
  def process(n: N, intra: Boolean): Unit

  /** Adds an item to the worklist.
    */
  def add(n: N): Unit

  /** Adds a set of items to the worklist.
    */
  def add(ns: Iterable[N]): Unit

  /** Iterates until there is no more work to do.
    *
    * @param first
    *   the initial contents of the worklist
    */
  def run(first: Set[N], intra: Boolean): Unit

/** A simple n^2 worklist algorithm based on `scala.collection.immutable.ListSet`.
  *
  * @tparam N
  *   type of the elements in the worklist.
  *
  * Note: 
  *  add(m) is O(n * m)
  *  worklist.run() is O(|first|^2)
  *    - ListSet.tail() and ListSet.head() are both O(n)
  */
trait ListSetWorklist[N] extends Worklist[N]:

  private var worklist = new ListSet[N]

  def add(n: N) =
    worklist += n

  def add(ns: Iterable[N]) = worklist ++= ns

  def run(first: Set[N], intra: Boolean) =
    worklist = new ListSet[N] ++ first
    while worklist.nonEmpty do
      val n = worklist.head
      worklist = worklist.tail
      process(n, intra)


/** A more performant worklist algorithm.
  *
  * @tparam N
  *   type of the elements in the worklist.
  */
trait LinkedHashSetWorklist[N] extends Worklist[N]:
  private val worklist = new LinkedHashSet[N]

  def add(n: N) =
    worklist += n

  def add(ns: Iterable[N]) = worklist ++= ns

  def run(first: Set[N], intra: Boolean) =
    worklist.addAll(first);
    while (worklist.nonEmpty) do
      val n = worklist.head;
      worklist.remove(n)
      process(n, intra)


/** Priority Queue Worklist
  *
  * Assumes nodes have unique priorities and
  * will only process a node once, regardless of the
  * number of times it is queued. Will process the
  * node again if it is queued AFTER its been processed.
  *
  * Single processing is generally desirable in a worklist
  * solver, as repeated processing of a node without intermediate
  * modifications to its incoming state will be redundant.
  *
  * @tparam N
  *   type of the elements in the worklist.
  */
trait PriorityQueueWorklist[N] extends Worklist[N] with Priorities[N]:
  //implicit val ord: Ordering[N] = Ordering.by( e => e.asInstanceOf[CfgNode].rpo )
  private val worklist = new PriorityQueue[N]()
  def add(n: N) = worklist += n
  def add(ns: Iterable[N]) = worklist ++= ns

  def run(first: Set[N], intra: Boolean) = {
    worklist ++= first
    while (worklist.nonEmpty) do {
      val n = worklist.dequeue()
      /** Drop all items in the queue with the same priority.
        * n is already the greatest, so head >= n implies n == head.
        */
      while (worklist.nonEmpty && !ord.lt(worklist.head,n)) do {
        val m = worklist.dequeue()
        assert(m == n, s"Different nodes with same priority, violates PriorityQueueWorklist assumption: $n and $m")
      }
      process(n, intra)
    }
  }


/** Base trait for worklist-based fixpoint solvers.
  *
  * @tparam N
  *   type of the elements in the worklist.
  */
trait WorklistFixpointSolver[N] extends MapLatticeSolver[N] with LinkedHashSetWorklist[N] with Dependencies[N]:
  /** The current lattice element.
    */
  var x: lattice.Element = _

  def process(n: N, intra: Boolean) =
    val xn = x(n)
    val y = funsub(n, x, intra)
    if y != xn then
      x += n -> y
      add(outdep(n, intra))

/** Worklist-based fixpoint solver.
  *
  * @tparam N
  *   type of the elements in the worklist.
  */
trait SimpleWorklistFixpointSolver[N] extends WorklistFixpointSolver[N]:

  /** The map domain.
    */
  val domain: Set[N]

  /** Push the results of the analysis one node down. This is used to have the results of the pre node in the current
    * node.
    * @param the
    *   current lattice
    * @return
    *   the new lattice element
    */

  def analyze(intra: Boolean): lattice.Element =
    x = lattice.bottom
    run(domain, intra)
    x

/** A pushDown worklist-based fixpoint solvers. Pushes the results of the analysis one node down. This is used to have
  * the results of the pred node in the current node. ie. NODE 1: R0 = 69551bv64 RESULT LATTICE = {} NODE 2: R0 =
  * MemLoad[R0 + 54bv64] RESULT LATTICE = {R0 = 69551bv64} NODE 3: R1 = 0bv64 RESULT LATTICE = {R0 = TOP} ...
  *
  * @tparam N
  *   type of the elements in the worklist.
  *
  * Better implementation of the same thing
  * https://github.com/cs-au-dk/TIP/blob/master/src/tip/solvers/FixpointSolvers.scala#L311
  */
trait PushDownWorklistFixpointSolver[N] extends MapLatticeSolver[N] with PriorityQueueWorklist[N] with Dependencies[N]:
  /** The current lattice element.
    */
  var x: lattice.Element = _

  /** Propagates lattice element y to node m.
    * https://github.com/cs-au-dk/TIP/blob/master/src/tip/solvers/FixpointSolvers.scala#L286
    */
  def propagate(y: lattice.sublattice.Element, m: N, intra: Boolean): Unit = {
    val xm = x(m)
    /* If we are the successors only predecessor, simply overwrite */
    val t = if indep(m, intra).size > 1 then lattice.sublattice.lub(xm, y) else y
    if (t != xm) {
      add(m)
      x += m -> t
    }
  }

  def process(n: N, intra: Boolean) =
    val xn = x(n)
    var y = transfer(n, xn)
    var next = outdep(n, intra)

    /** Process all nodes that are trivially linked to the current
      * such that the next node is the current's only successor and
      * the current is the next node's only predecessor.
      * Effectively emulating a basic block.
      */
    while (next.size == 1 && indep(next.head, intra).size <= 1) {
      val succ = next.head
      val xm = x(succ)
      if (y == xm) {
        /* Reached a fixed point, no need to progress */
        return
      } else {
        /* Stash the state and continue */
        x += succ -> y
        y = transfer(succ, y)
        next = outdep(succ, intra)
      }
    }

    /* End of the block, propagate onwards */
    for succ <- next do propagate(y, succ, intra)

/** Worklist-based fixpoint solver.
  *
  * @tparam N
  *   type of the elements in the worklist.
  */
trait SimplePushDownWorklistFixpointSolver[N] extends PushDownWorklistFixpointSolver[N]:

  /** The map domain.
    */
  val domain: Set[N]

  /** Push the results of the analysis one node down. This is used to have the results of the pre node in the current
    * node.
    * @param the
    *   current lattice
    * @return
    *   the new lattice element
    */

  def analyze(intra: Boolean): lattice.Element =
    x = lattice.bottom
    run(domain, intra)
    x
