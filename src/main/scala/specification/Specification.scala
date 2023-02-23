package specification

import boogie._
import ir._

trait SpecVar extends BExpr {
  override def specVars: Set[SpecVar] = Set(this)
  override def getType: BType = {
    println(this)
    ???
  }
  override def replaceReserved(reserved: Set[String]): BExpr = this
}

case class SpecGlobal(name: String, size: Int, address: BigInt) extends SpecVar {
  val toAddrVar: BVar = BVariable("$" + s"${name}_addr", BitVecBType(64), Scope.Const)
  val toOldVar: BVar = BVariable(s"${name}_old", BitVecBType(size), Scope.Local)
  val toOldGamma: BVar = BVariable(s"Gamma_${name}_old", BoolBType, Scope.Local)
  val toAxiom: BAxiom = BAxiom(BinaryBExpr(BoolEQ, toAddrVar, BitVecBLiteral(address, 64)))
  override def resolveSpec: BMemoryLoad = BMemoryLoad(BMapVar("mem", MapBType(BitVecBType(64), BitVecBType(8)), Scope.Global), toAddrVar, Endian.LittleEndian, size)
  override def resolveOld: BMemoryLoad = resolveSpec
  override def removeOld: BMemoryLoad = resolveSpec
  override def resolveSpecL: BMemoryLoad = BMemoryLoad(BMapVar("memory", MapBType(BitVecBType(64), BitVecBType(8)), Scope.Parameter), toAddrVar, Endian.LittleEndian, size)
}

case class SpecGamma(global: SpecGlobal) extends SpecVar {
  // TODO don't hardcode this
  override def resolveSpec: GammaLoad = GammaLoad(BMapVar("Gamma_mem", MapBType(BitVecBType(64), BoolBType), Scope.Global), global.toAddrVar, global.size, global.size/8)
  override def resolveOld: GammaLoad = resolveSpec
  override def removeOld: GammaLoad = resolveSpec
  override def resolveSpecL: GammaLoad = resolveSpec
}

case class Specification(globals: Set[SpecGlobal], LPreds: Map[SpecGlobal, BExpr], relies: List[BExpr], guarantees: List[BExpr], subroutines: List[SubroutineSpec]) {
  val guaranteeOldVars: List[SpecGlobal] = guarantees.flatMap(g => g.oldSpecVars.collect{ case s: SpecGlobal => s })

  val controls: Map[SpecGlobal, Set[SpecGlobal]] = {
    val controlledBy = LPreds.map((k, v) => k -> v.specVars.collect{ case s: SpecGlobal => s }).collect{ case (k, v) if v.nonEmpty => (k, v) }
    controlledBy.toSet.flatMap((k, v) => v.map(_ -> k)).groupMap(_._1)(_._2)
  }
  val controlled: Set[SpecGlobal] = controls.values.flatten.toSet
}

case class SubroutineSpec(name: String, requires: List[BExpr], ensures: List[BExpr])

case class ExternalFunction(name: String, offset: BigInt)