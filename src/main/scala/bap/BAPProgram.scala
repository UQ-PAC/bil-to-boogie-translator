package bap

import ir._

case class BAPProgram(subroutines: List[BAPSubroutine]) {
  override def toString: String = subroutines.mkString("\n")

  /*
  def getFunction(name: String): Option[BAPSubroutine] = {
    subroutines.find(f => f.name == name)
  }

  def getFunction(address: Int): Option[BAPSubroutine] = {
    subroutines.find(f => f.address == address)
  }
  */
}

case class BAPSubroutine(name: String, address: Int, blocks: List[BAPBlock], in: List[BAPParameter], out: List[BAPParameter]) {
  override def toString: String = name + " " + address + " " + in + " " + out + "[\n" + blocks.mkString("\n") + "\n]"

  /*
  def calls: Set[String] = blocks.flatMap(b => b.calls).toSet

  def getBlock(label: String): Option[BAPBlock] = {
    blocks.find(b => b.label == label)
  }
  */
}

case class BAPBlock(label: String, address: Option[Int], statements: List[BAPStatement], jumps: List[BAPJump]) {
  override def toString: String = label + " " + address + "\n" + statements.mkString("\n")
  /*
  def modifies: Set[BAPMemory] = statements.flatMap(_.modifies).toSet

  def locals: Set[BAPLocalVar] = statements.flatMap(_.locals).toSet
  def calls: Set[String] = statements.flatMap(_.calls).toSet
  */

}

case class BAPParameter(name: String, size: Int, value: BAPLocalVar) {
  def toIR: Parameter = Parameter(name, size, value.toIR)
}