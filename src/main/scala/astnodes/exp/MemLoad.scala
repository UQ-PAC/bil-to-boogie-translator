package astnodes.exp

import java.util.Collections
import java.util
import java.util.Objects
import astnodes.pred
import astnodes.pred.conjunct
import astnodes.exp.Var;

/** Memory expression e.g. mem[10]
  */
case class MemLoad(var exp: Expr, override val size: Some[Int]) extends Expr {

  override def toString = s"${if (this.onStack) "stack" else "heap"}[$exp]"

  // TODO this is a mess
  def toBoogieString(exp: Expr) = s"${if (this.onStack) "stack" else "heap"}[${exp.toBoogieString}]"
  override def toBoogieString: String =
    (0 to size.get/8 - 1).map(n => s"${toBoogieString(BinOp(BinOperator.Addition, exp, Literal(n.toString)))}")
      .mkString(" ++ ")

  override def getChildren = Collections.singletonList(exp)
  override def replace(oldExp: Expr, newExp: Expr) = if (exp == oldExp) exp = newExp

  override def vars = List(this) // TOOD also exp.vars????

  /** Assumes: anything on the stack is represented as SP + val (where val is an int etc)
    */
  def onStack = exp match {
<<<<<<< HEAD
    // TODO improve once everything is immutable
    case BinOp(_, v: Var, _) => v.name == "SP"
=======
    case v: Var => v.name == "R31"
    case BinOp(_, v: Var, _) => v.name == "R31"
>>>>>>> 8dc2e6ed607444f1c25f7b0b36ea251216459046
    case _ => false
  }

  // TODO need to rework memload .....
  def toL = new pred.MemLoad(false, true, exp)
  def toGamma = new pred.MemLoad(true, false, exp)
}
