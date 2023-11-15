package analysis

/** Dependency methods for worklist-based analyses.
  */
trait Dependencies[N]:

  /** Outgoing dependencies. Used when propagating dataflow to successors.
    * @param n
    *   an element from the worklist
    * @return
    *   the elements that depend on the given element
    */
  def outdep(n: N): Set[N]

  /** Incoming dependencies. Used when computing the join from predecessors.
    * @param n
    *   an element from the worklist
    * @return
    *   the elements that the given element depends on
    */
  def indep(n: N): Set[N]

trait InterproceduralForwardDependencies extends Dependencies[CfgNode] {
  def outdep(n: CfgNode): Set[CfgNode] = n.succ(false).toSet.union(n.succ(true).toSet)
  def indep(n: CfgNode): Set[CfgNode] = n.pred(false).toSet.union(n.pred(true).toSet)
}

trait IntraproceduralForwardDependencies extends Dependencies[CfgNode] {
  def outdep(n: CfgNode): Set[CfgNode] = n.succ(true).toSet
  def indep(n: CfgNode): Set[CfgNode] = n.pred(true).toSet
}