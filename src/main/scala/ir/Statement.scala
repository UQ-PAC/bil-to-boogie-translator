package ir
import intrusivelist.IntrusiveListElement

import collection.mutable

/*
  To support the state-free IL iteration in CFG order all Commands must be classes with a unique object ref.
*/

sealed trait Command extends HasParent[Block] {
  val label: Option[String]

  def labelStr: String = label match {
    case Some(s) => s"$s: "
    case None => ""
  }

}

sealed trait Statement extends Command, HasParent[Block], IntrusiveListElement[Statement] {
  def modifies: Set[Global] = Set()
  //def locals: Set[Variable] = Set()
  def acceptVisit(visitor: Visitor): Statement = throw new Exception(
    "visitor " + visitor + " unimplemented for: " + this
  )
}

class LocalAssign(var lhs: Variable, var rhs: Expr, override val label: Option[String] = None) extends Statement {
  //override def locals: Set[Variable] = rhs.locals + lhs
  override def modifies: Set[Global] = lhs match {
    case r: Register => Set(r)
    case _           => Set()
  }
  override def toString: String = s"$labelStr$lhs := $rhs"
  override def acceptVisit(visitor: Visitor): Statement = visitor.visitLocalAssign(this)
}

object LocalAssign:
  def unapply(l: LocalAssign): Option[(Variable, Expr, Option[String])] = Some(l.lhs, l.rhs, l.label)

class MemoryAssign(var lhs: Memory, var rhs: MemoryStore,  override val label: Option[String] = None) extends Statement {
  override def modifies: Set[Global] = Set(lhs)
  //override def locals: Set[Variable] = rhs.locals
  override def toString: String = s"$labelStr$lhs := $rhs"
  override def acceptVisit(visitor: Visitor): Statement = visitor.visitMemoryAssign(this)
}

object MemoryAssign:
  def unapply(m: MemoryAssign): Option[(Memory, MemoryStore, Option[String])] = Some(m.lhs, m.rhs, m.label)

class NOP(override val label: Option[String] = None) extends Statement {
  override def toString: String = s"NOP $labelStr"
  override def acceptVisit(visitor: Visitor): Statement = this
}

class Assert(var body: Expr, var comment: Option[String] = None, override val label: Option[String] = None) extends Statement {
  override def toString: String = s"${labelStr}assert $body" + comment.map(" //" + _)
  override def acceptVisit(visitor: Visitor): Statement = visitor.visitAssert(this)
}

object Assert:
  def unapply(a: Assert): Option[(Expr, Option[String], Option[String])] = Some(a.body, a.comment, a.label)

  /**
   * checkSecurity is true if this is a branch condition that we want to assert has a security level of low before branching
   * */
class Assume(var body: Expr, var comment: Option[String] = None, override val label: Option[String] = None, var checkSecurity: Boolean = false) extends Statement {

  override def toString: String = s"${labelStr}assume $body" + comment.map(" //" + _)
  override def acceptVisit(visitor: Visitor): Statement = visitor.visitAssume(this)
}

object Assume:
  def unapply(a: Assume): Option[(Expr, Option[String], Option[String], Boolean)] = Some(a.body, a.comment, a.label, a.checkSecurity)

sealed trait Jump extends Command, HasParent[Block]  {
  def modifies: Set[Global] = Set()
  //def locals: Set[Variable] = Set()
  def calls: Set[Procedure] = Set()
  def acceptVisit(visitor: Visitor): Jump = throw new Exception("visitor " + visitor + " unimplemented for: " + this)
}



class GoTo private (private var _targets: mutable.Set[Block], override val label: Option[String]) extends Jump {

  def this(targets: Iterable[Block], label: Option[String] = None) = this(mutable.Set.from(targets), label)

  def targets: Set[Block] = _targets.toSet

  def addAllTargets(t: Iterable[Block]): Unit = {
    t.foreach(addTarget(_))
  }

  def addTarget(t: Block): Unit = {
    if (_targets.add(t)) {
      t.addIncomingJump(this)
    }
  }

  override def linkParent(b: Block): Unit = {
    _targets.foreach(_.addIncomingJump(this))
  }

  override def unlinkParent(): Unit = {
    targets.foreach(_.removeIncomingJump(this))
  }


  def removeTarget(t: Block): Unit = {
    // making the assumption that blocks only contain the same outgoing edge once
    //  e.g. We don't have two edges going to the same block under different conditions
    if (_targets.remove(t)) {
      t.removeIncomingJump(this)
    }
  }


  override def toString: String = s"${labelStr}NonDetGoTo(${targets.map(_.label).mkString(", ")})"
  override def acceptVisit(visitor: Visitor): Jump = visitor.visitGoTo(this)
}

object GoTo:
  def unapply(g: GoTo): Option[(Set[Block], Option[String])] = Some(g.targets, g.label)


sealed trait Call extends Jump

trait FallThrough extends Call: 
  /**
   * Manages the fallthrough block for a call.
   *
   *  There is a aftercall block inserted after each call, which is visited after the call in the cfg 
   *
   *  Replacing the return target of the call replaces the aftercall block. 
   */

  private var _afterCall: Option[Block] = None
  private var _returnTarget: Option[Block] = None


  // replacing the return target of a call
  def returnTarget_=(b: Block) : Unit = {
    require(b.hasParent)

    if (hasParent) {
      // if we don't have a parent now, delay adding the fallthrough block until linking
      linkParent(parent)
    }
    _returnTarget = Some(b) 
  }

  def returnTarget: Option[Block] = _returnTarget

  def afterCall: Option[Block] = _afterCall 
  
  // moving a call between blocks
  override def linkParent(p: Block): Unit = {
    _afterCall = _returnTarget.map(b => (p.parent.addBlocks(Block.afterCall(this, Some(b)))))
    _afterCall.foreach(parent.parent.addBlocks(_))
  }

  override def unlinkParent(): Unit = {
    _afterCall.foreach(ac => {parent.parent.removeBlocks(ac)})
  }


class DirectCall(val target: Procedure, private val _returnTarget: Option[Block] = None,  override val label: Option[String] = None) extends Call with FallThrough {
  _returnTarget.foreach(x => returnTarget = x) 
  /* override def locals: Set[Variable] = condition match {
    case Some(c) => c.locals
    case None => Set()
  } */
  override def calls: Set[Procedure] = Set(target)
  override def toString: String = s"${labelStr}DirectCall(${target.name}, ${returnTarget.map(_.label)})"
  override def acceptVisit(visitor: Visitor): Jump = visitor.visitDirectCall(this)

  override def linkParent(p: Block): Unit = {
    super.linkParent(p)
    target.addCaller(this)
  }

  override def unlinkParent(): Unit = {
    super.unlinkParent()
    target.removeCaller(this)
  }

}

object DirectCall:
  def unapply(i: DirectCall): Option[(Procedure,  Option[Block], Option[String])] = Some(i.target, i.returnTarget, i.label)

class IndirectCall(var target: Variable, private val _returnTarget: Option[Block] = None, override val label: Option[String] = None) extends Call with FallThrough{
  _returnTarget.foreach(x => returnTarget = x) 
  /* override def locals: Set[Variable] = condition match {
    case Some(c) => c.locals + target
    case None => Set(target)
  } */
  override def toString: String = s"${labelStr}IndirectCall($target, ${returnTarget.map(_.label)})"
  override def acceptVisit(visitor: Visitor): Jump = visitor.visitIndirectCall(this)
}

object IndirectCall:
  def unapply(i: IndirectCall): Option[(Variable, Option[Block], Option[String])] = Some(i.target, i.returnTarget, i.label)
