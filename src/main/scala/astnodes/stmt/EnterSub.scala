package astnodes.stmt

import astnodes.parameters.InParameter
import astnodes.exp.Expr
import astnodes.exp.`var`.Var
import astnodes.parameters.OutParameter

import scala.jdk.CollectionConverters.*
import java.util
import java.util.*
import scala.collection.immutable

// TODO scalaify
// TODO rewrite statment loader to remove getters
case class EnterSub(override val pc: String, var funcName: String) extends Stmt(pc) {
  private var inParams: List[InParameter] = new util.ArrayList[InParameter]()
  private var outParam: Option[OutParameter] = None
  private var modifies: List[String] = new util.LinkedList[String]() // TODO type
  // TODO dont like this
  modifies.addAll(immutable.List("heap", "stack", "Gamma_heap", "Gamma_stack", "SP", "R31", "Gamma_SP", "Gamma_R31").asJava)

  def getInParams = inParams
  def getOutParam = outParam
  def setOutParam(outParam: OutParameter) = this.outParam = Some(outParam)
  def setInParams(newInParms: List[InParameter]) = inParams = newInParms
  def getFuncName = funcName

  override def toString = {
    val in = inParams.asScala.mkString(", ")
    val out = if (outParam != None) f" returns (${outParam.get})" else ""

    val decl = funcName + "(" + in + ")" + out

    // TODO
    val modifiesStr =
      if (modifies.size > 0) "\n modifies " + modifies.asScala.mkString(", ") //+ ";\nimplementation " + decl
      else ""

    "procedure " + decl + modifiesStr + "; {"
  }

  override def subst(v: Var, w: Var): Stmt = this
}
