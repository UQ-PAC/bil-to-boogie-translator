package astnodes
import boogie._

trait Statement {
  //def subst(v: Variable, w: Variable): Stmt

  //def toBoogieString: String = toString
  def modifies: Set[Memory] = Set()
  def locals: Set[LocalVar] = Set()
  def calls: Set[String] = Set() // names of functions called by this statement

  /*
  def labelString: String = if (labelVisible) {
    "label" + pc + ": "
  } else {
    ""
  }
   */

  //def withVisibleLabel: Stmt
}

class DirectCall(var target: String, var condition: Expr, var returnTarget: Option[String], var line: String, var instruction: String) extends Statement {
  /*
  override def toBoogieString: String = {
    if (condition == Literal(BigInt(1), 1)) {
      noCondition
    } else {
      "if (" + condition.toBoogieString + " == 0bv1) {\n      " + noCondition + "\n    }"
    }
  }
  def noCondition: String = "call " + target + "(); // with return " + returnTarget.getOrElse("none")
   */

  override def calls: Set[String] = Set(target)
  override def locals: Set[LocalVar] = condition.locals

  override def toString: String = String.format("call %s(); // with return %s", target, returnTarget.getOrElse("none"))
}

class IntrinsicCall(var target: String, var condition: Expr, var returnTarget: Option[String], var line: String, var instruction: String) extends Statement {

  override def calls: Set[String] = Set(target)
  override def locals: Set[LocalVar] = condition.locals
}

class IndirectCall(var target: LocalVar, var condition: Expr, var returnTarget: Option[String], var line: String, var instruction: String) extends Statement {
  /*
  override def toBoogieString: String = {
    if (condition == Literal(BigInt(1), 1)) {
      noCondition
    } else {
      "if (" + condition.toBoogieString + " == 0bv1) {\n      " + noCondition + "\n    }"
    }
  }
  def noCondition: String = "call " + target.toBoogieString + "; // with return " + returnTarget.getOrElse("none")
   */

  override def locals: Set[LocalVar] = condition.locals + target

  override def toString: String = String.format("call %s(); // with return %s", target, returnTarget.getOrElse("none"))
}

class GoTo(var target: String, var condition: Expr, var line: String, var instruction: String) extends Statement {
  /*
  override def toBoogieString: String = {
    if (condition == Literal(BigInt(1), 1)) {
      noCondition
    } else {
      "if (" + condition.toBoogieString + " == 0bv1) {\n      " + noCondition + "\n    }"
    }
  }
  def noCondition: String = "goto " + target + ";"
   */

  override def locals: Set[LocalVar] = condition.locals

  override def toString: String = String.format("goto %s;", target)
}

class Skip(var line: String, var instruction: String) extends Statement {
  override def toString: String = "skip;"
  //override def subst(v: Variable, w: Variable): Stmt = this

  //override def withVisibleLabel: Stmt = copy(labelVisible = true)

}

trait Assign(lhs: Variable, rhs: Expr, line: String, instruction: String) extends Statement {
  override def toString: String = String.format("%s := %s;", lhs, rhs)

  /*
  override def subst(v: Variable, w: Variable): Stmt = lhs.subst(v,w) match {
    case lhsRes: MemLoad => MemAssign(pc, lhsRes, rhs.subst(v,w))
    case lhsRes: Register => RegisterAssign(pc, lhsRes, rhs = rhs.subst(v,w))
  }
   */

  // this would be nicer to have per type instead
  /*
  def simplify(oldExpr: Expr, newExpr: Expr): AssignStatement = {
    lhs match {
      case lhsRes: MemAccess =>
        val newLhs = if (!lhsRes.onStack) {
          lhsRes.simplify(oldExpr, newExpr).asInstanceOf[MemAccess]
        } else {
          lhsRes
        }
        MemAssign(newLhs, rhs.simplify(oldExpr, newExpr))
      case lhsRes: LocalVar => LocalAssign(lhsRes, rhs.simplify(oldExpr, newExpr))
      case _ => this
    }
  }
   */
}

/*
case class GammaUpdate (lhs: SecVar | SecMemLoad, sec: Sec) extends Statement {

  override def toBoogieString: String = s"${lhs.toString} := ${sec.toString};"

  override def modifies: Set[Memory] = Set()
  override def locals: Set[LocalVar] = Set()

  // TODO
  //override def subst(v: Variable, w: Variable): Stmt = this
}
 */

/** Memory store
  */
class MemAssign(var lhs: Memory, var rhs: Store, var line: String, var instruction: String) extends Assign(lhs, rhs, line, instruction) {

  //override def toBoogieString: String = s"${lhs.toBoogieString} := ${rhs.toBoogieString};"
  /*
  def lhsToString(exp: Expr) = s"heap[${exp.toBoogieString}]"

  override def toBoogieString: String = {
    (0 until lhs.size / 8).map(n => {
      s"heap[${lhs.index.toBoogieString} + $n] := ${Extract(8 * (n + 1) - 1, 8 * n, rhs).toBoogieString}"
    }).mkString("; ") + s";"
  }
   */

  override def modifies: Set[Memory] = Set(lhs)

  override def locals: Set[LocalVar] = rhs.locals
}

object MemAssign {
  def init(lhs: Memory, rhs: Store, line: String, instruction: String): MemAssign = {
    if (rhs.memory.name == "stack") {
      MemAssign(lhs.copy(name = "stack"), rhs, line, instruction)
    } else {
      MemAssign(lhs, rhs, line, instruction)
    }
  }
}

class LocalAssign(var lhs: LocalVar, var rhs: Expr, var line: String, var instruction: String) extends Assign(lhs, rhs, line, instruction) {
  //override def toBoogieString: String = s"${lhs.toBoogieString} := ${rhs.toBoogieString};"

  // Otherwise is flag (e.g. #1)
  /*
  def isRegister: Boolean = lhs.name.charAt(0) == 'R'

  def isStackPointer: Boolean = this.isRegister && lhs.name.substring(1).equals("31")
  def isFramePointer: Boolean = this.isRegister && lhs.name.substring(1).equals("29")
  def isLinkRegister: Boolean = this.isRegister && lhs.name.substring(1).equals("30")
   */
  override def locals: Set[LocalVar] = rhs.locals + lhs

}
