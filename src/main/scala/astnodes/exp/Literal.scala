package astnodes.exp

import java.util
import java.util.Objects

/** Literal expression (e.g. 4, 5, 10)
  */
case class Literal(var value: String) extends Expr {
  this.value = parseHex(value)

  /** Value of literal */
  private def parseHex(value: String): String = {
    if (value == null) value // null literals can be useful for analyses as a special "no value" case, different to "0"
    else if (value.length < 3 || !(value.substring(0, 2) == "0x")) value
    else java.lang.Long.toUnsignedString(java.lang.Long.parseUnsignedLong(value.substring(2), 16))
  }
  override def toString = String.format("%s", value)
  override def getChildren = new util.ArrayList[Expr]
  override def replace(oldExp: Expr, newExp: Expr) = {}

  override def vars: List[Var] = List()

  override def toBoogieString: String = value + "bv64"
}
