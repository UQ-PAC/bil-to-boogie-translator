package translating
import ir._
import boogie._
import specification._

import scala.collection.mutable.ArrayBuffer

class IRToBoogie(var program: Program, var spec: Specification) {
  private val globals = spec.globals
  private val controls = spec.controls
  private val controlled = spec.controlled
  private val relies = spec.relies.map(r => r.resolveSpec)
  private val reliesReflexive = spec.relies.map(r => r.removeOld)
  private val guarantees = spec.guarantees.map(g => g.resolveOld)
  private val guaranteesReflexive = spec.guarantees.map(g => g.removeOld)
  private val guaranteeOldVars = spec.guaranteeOldVars
  private val LPreds = spec.LPreds.map((k, v) => k -> v.resolveSpecL)
  private val requires = spec.subroutines.map(s => s.name -> s.requires.map(e => e.resolveSpec)).toMap
  private val requiresDirect = spec.subroutines.map(s => s.name -> s.requiresDirect).toMap
  private val ensures = spec.subroutines.map(s => s.name -> s.ensures.map(e => e.resolveSpec)).toMap
  private val ensuresDirect = spec.subroutines.map(s => s.name -> s.ensuresDirect).toMap
  private val directFunctions = spec.directFunctions

  private val mem = BMapVar("mem", MapBType(BitVecBType(64), BitVecBType(8)), Scope.Global)
  private val Gamma_mem = BMapVar("Gamma_mem", MapBType(BitVecBType(64), BoolBType), Scope.Global)
  private val stack = BMapVar("stack", MapBType(BitVecBType(64), BitVecBType(8)), Scope.Global)
  private val Gamma_stack = BMapVar("Gamma_stack", MapBType(BitVecBType(64), BoolBType), Scope.Global)

  def translate: BProgram = {
    val procedures = program.procedures.map(f => translateProcedure(f))
    // TODO remove this once proper analysis for modifies is done
    val defaultGlobals = List(BVarDecl(mem), BVarDecl(Gamma_mem), BVarDecl(stack), BVarDecl(Gamma_stack))
    val globalDecls = (procedures.flatMap(p => p.globals).map(b => BVarDecl(b)) ++ defaultGlobals).distinct.sorted.toList

    val globalConsts: List[BConstAxiomPair] = globals.map(g => BConstAxiomPair(BVarDecl(g.toAddrVar), g.toAxiom)).toList.sorted


    val guaranteeReflexive = BProcedure("guarantee_reflexive", List(), List(), List(), List(), List(), List(), Seq(mem, Gamma_mem), guaranteesReflexive.map(g => BAssert(g)))

    val rgProcs = genRely(relies) :+ guaranteeReflexive

    val functionsUsed1 = procedures.flatMap(p => p.functionOps).toSet ++ rgProcs.flatMap(p => p.functionOps).toSet ++ directFunctions
    val functionsUsed2 = functionsUsed1.map(p => functionOpToDefinition(p))
    val functionsUsed3 = functionsUsed2.flatMap(p => p.functionOps).map(p => functionOpToDefinition(p))
    val functionsUsed = (functionsUsed2 ++ functionsUsed3).toList.sorted

    val declarations = globalDecls ++ globalConsts ++ functionsUsed ++ rgProcs ++ procedures
    BProgram(declarations)
  }

  def genRely(relies: List[BExpr]): List[BProcedure] = {
    val reliesUsed = if (relies.nonEmpty) {
      relies
    } else {
      // default case where no rely is given - rely on no external changes
      List(BinaryBExpr(BVEQ, mem, Old(mem)), BinaryBExpr(BVEQ, Gamma_mem, Old(Gamma_mem)))
    }
    val i = BVariable("i", BitVecBType(64), Scope.Local)
    val rely2 = ForAll(List(i), BinaryBExpr(BoolIMPLIES, BinaryBExpr(BVEQ, MapAccess(mem, i), Old(MapAccess(mem, i))), BinaryBExpr(BVEQ, MapAccess(Gamma_mem, i), Old(MapAccess(Gamma_mem, i)))))
    val relyEnsures = List(rely2) ++ reliesUsed
    val relyProc = BProcedure("rely", List(), List(), relyEnsures, List(), List(), List(), Seq(mem, Gamma_mem), List())
    val relyTransitive = BProcedure("rely_transitive", List(), List(), reliesUsed, List(), List(), List(), Seq(mem, Gamma_mem), List(ProcedureCall("rely", List(), List(), List(mem, Gamma_mem)), ProcedureCall("rely", List(), List(), List(mem, Gamma_mem))))
    val relyReflexive = BProcedure("rely_reflexive", List(), List(), List(), List(), List(), List(), Seq(), reliesReflexive.map(r => BAssert(r)))
    List(relyProc, relyTransitive, relyReflexive)
  }

  def functionOpToDefinition(f: FunctionOp): BFunction = {
    f match {
      case b: BVFunctionOp => BFunction(b.name, b.bvbuiltin, b.in, b.out, None)
      case m: MemoryLoadOp =>
        val memVar = BMapVar("memory", MapBType(BitVecBType(m.addressSize), BitVecBType(m.valueSize)), Scope.Parameter)
        val indexVar = BParam("index", BitVecBType(m.addressSize))
        val in = List(memVar, indexVar)
        val out = BParam(BitVecBType(m.bits))
        val accesses: Seq[MapAccess] = for (i <- 0 until m.accesses) yield {
          if (i == 0) {
            MapAccess(memVar, indexVar)
          } else {
            MapAccess(memVar, BinaryBExpr(BVADD, indexVar, BitVecBLiteral(i, m.addressSize)))
          }
        }
        val accessesEndian = m.endian match {
          case Endian.BigEndian => accesses.reverse
          case Endian.LittleEndian => accesses
        }

        val body: BExpr = accessesEndian.tail.foldLeft(accessesEndian.head) {
          (concat: BExpr, next: MapAccess) => BinaryBExpr(BVCONCAT, next, concat)
        }

        BFunction(m.fnName, "", in, out, Some(body))
      case g: GammaLoadOp =>
        val gammaMapVar = BMapVar("gammaMap", MapBType(BitVecBType(g.addressSize), BoolBType), Scope.Parameter)
        val indexVar = BParam("index", BitVecBType(g.addressSize))
        val in = List(gammaMapVar, indexVar)
        val out = BParam(BoolBType)
        val accesses: Seq[MapAccess] = for (i <- 0 until g.accesses) yield {
          if (i == 0) {
            MapAccess(gammaMapVar, indexVar)
          } else {
            MapAccess(gammaMapVar, BinaryBExpr(BVADD, indexVar, BitVecBLiteral(i, g.addressSize)))
          }
        }

        val body: BExpr = accesses.tail.foldLeft(accesses.head) {
          (and: BExpr, next: MapAccess) => BinaryBExpr(BoolAND, next, and)
        }

        BFunction(g.fnName, "", in, out, Some(body))
      case m: MemoryStoreOp =>
        val memType = MapBType(BitVecBType(m.addressSize), BitVecBType(m.valueSize))
        val memVar = BMapVar("memory", memType, Scope.Parameter)
        val indexVar = BParam("index", BitVecBType(m.addressSize))
        val valueVar = BParam("value", BitVecBType(m.bits))
        val in = List(memVar, indexVar, valueVar)
        val out = BParam(memType)
        val indices: Seq[BExpr] = for (i <- 0 until m.accesses) yield {
          if (i == 0) {
            indexVar
          } else {
            BinaryBExpr(BVADD, indexVar, BitVecBLiteral(i, m.addressSize))
          }
        }
        val values: Seq[BExpr] = for (i <- 0 until m.accesses) yield {
          BVExtract((i + 1) * m.valueSize, i * m.valueSize, valueVar)
        }
        val valuesEndian = m.endian match {
          case Endian.BigEndian => values.reverse
          case Endian.LittleEndian => values
        }
        val indiceValues = for (i <- 0 until m.accesses) yield {
          (indices(i), valuesEndian(i))
        }

        val body: MapUpdate = indiceValues.tail.foldLeft(MapUpdate(memVar, indices.head, valuesEndian.head)) {
          (update: MapUpdate, next: (BExpr, BExpr)) => MapUpdate(update, next._1, next._2)
        }

        BFunction(m.fnName, "", in, out, Some(body))
      case g: GammaStoreOp =>
        val gammaMapType = MapBType(BitVecBType(g.addressSize), BoolBType)
        val gammaMapVar = BMapVar("gammaMap", gammaMapType, Scope.Parameter)
        val indexVar = BParam("index", BitVecBType(g.addressSize))
        val valueVar = BParam("value", BoolBType)
        val in = List(gammaMapVar, indexVar, valueVar)
        val out = BParam(gammaMapType)

        val indices: Seq[BExpr] = for (i <- 0 until g.accesses) yield {
          if (i == 0) {
            indexVar
          } else {
            BinaryBExpr(BVADD, indexVar, BitVecBLiteral(i, g.addressSize))
          }
        }
        val values: Seq[BExpr] = for (i <- 0 until g.accesses) yield {
          valueVar
        }
        val indiceValues = for (i <- 0 until g.accesses) yield {
          (indices(i), values(i))
        }

        val body: MapUpdate = indiceValues.tail.foldLeft(MapUpdate(gammaMapVar, indices.head, values.head)) {
          (update: MapUpdate, next: (BExpr, BExpr)) => MapUpdate(update, next._1, next._2)
        }

        BFunction(g.fnName, "", in, out, Some(body))
      case l: LOp =>
        val memoryVar = BParam("memory", l.memoryType)
        val indexVar = BParam("index", l.indexType)
        val body: BExpr = LPreds.keys.foldLeft(FalseBLiteral) {
          (ite: BExpr, next: SpecGlobal) => {
            val guard = next.arraySize match {
              case Some(size: Int) =>
                val initial: BExpr = BinaryBExpr(BoolEQ, indexVar, ArrayAccess(next, 0).toAddrVar)
                val indices = 1 until size
                indices.foldLeft(initial) {
                  (or: BExpr, i: Int) => {
                    BinaryBExpr(BoolOR, BinaryBExpr(BoolEQ, indexVar, ArrayAccess(next, i).toAddrVar), or)
                  }
                }
              case None => BinaryBExpr(BoolEQ, indexVar, next.toAddrVar)
            }
            val LPred = LPreds(next)
            /*if (controlled.contains(next)) {
            FunctionCall(s"L_${next.name}", List(l.memory), BoolType)
          } else {
            LPreds(next)
          } */
            IfThenElse(guard, LPred, ite)
          }
        }
        BFunction("L", "", List(memoryVar, indexVar), BParam(BoolBType), Some(body))
    }
  }

  def translateProcedure(p: Procedure): BProcedure = {
    val in = p.in.flatMap(i => List(i.toBoogie, i.toGamma))

    var outRegisters: Set[Variable] = Set()

    val out = (for (o <- p.out) yield {
      if (outRegisters.contains(o.value)) {
        List()
      } else {
        outRegisters = outRegisters + o.value
        List(o.toBoogie, o.toGamma)
      }
    }).flatten

    outRegisters = Set()
    val returns = (for (o <- p.out) yield {
      if (outRegisters.contains(o.value)) {
        List()
      } else {
        outRegisters = outRegisters + o.value
        List(outParamToAssign(o))
      }
    }).flatten.toList

    val body = p.blocks.map(b => translateBlock(b, returns))
    //val modifies = p.modifies.map(m => m.name).toSeq.sorted
    val modifies = Seq(mem, Gamma_mem, stack, Gamma_stack) // TODO placeholder until proper modifies analysis

    val procRequires: List[BExpr] = if (p == program.mainProcedure) {
      requires.getOrElse(p.name, List()).prependedAll(initialiseMemory)
    } else {
      requires.getOrElse(p.name, List())
    }
    val procEnsures: List[BExpr] = ensures.getOrElse(p.name, List())

    val procRequiresDirect: List[String] = requiresDirect.getOrElse(p.name, List())
    val procEnsuresDirect: List[String] = ensuresDirect.getOrElse(p.name, List())

    val inInits = if (body.isEmpty) {
      List()
    } else {
      p.in.map(i => inParamToAssign(i)).toList
    }


    BProcedure(p.name, in.toList, out.toList, procEnsures, procRequires, procEnsuresDirect, procRequiresDirect, modifies, inInits ++ body.toList)
  }

  private def initialiseMemory: List[BExpr] = {
    val dataSections = program.initialMemory.collect {
      case s if s.name == ".data" || s.name == ".rodata" || s.name == ".got" => s
    }
    val sections = dataSections.flatMap { s =>
      for (b <- s.bytes.indices) yield {
        BinaryBExpr(BVEQ, BMemoryLoad(mem, BitVecBLiteral(s.address + b, 64), Endian.LittleEndian, 8), s.bytes(b).toBoogie)
      }
    }
    sections.toList
  }

  private def outParamToAssign(p: Parameter): AssignCmd = {
    val param = BParam(p.name, BitVecBType(p.size))
    val register = p.value.toBoogie
    val paramGamma = BParam(s"Gamma_${p.name}", BoolBType)
    val registerGamma = p.value.toGamma
    val assigned = if (p.size > p.value.size) {
      BVZeroExtend(p.size - p.value.size, register)
    } else if (p.size < p.value.size) {
      BVExtract(p.size, 0, register)
    } else {
      register
    }
    AssignCmd(List(param, paramGamma), List(assigned, registerGamma))
  }

  private def inParamToAssign(p: Parameter): AssignCmd = {
    val param = BParam(p.name, BitVecBType(p.size))
    val register = p.value.toBoogie
    val paramGamma = BParam(s"Gamma_${p.name}", BoolBType)
    val registerGamma = p.value.toGamma
    val assigned = if (p.size > p.value.size) {
      BVExtract(p.value.size, 0, param)
    } else if (p.size < p.value.size) {
      BVZeroExtend(p.value.size - p.size, param)
    } else {
      param
    }
    AssignCmd(List(register, registerGamma), List(assigned, paramGamma))
  }

  def translateBlock(b: Block, returns: List[BCmd]): BBlock = {
    val cmds = b.statements.flatMap(s => translate(s)) ++ b.jumps.flatMap(j => translate(j, returns))
    BBlock(b.label, cmds.toList)
  }

  def translate(j: Jump, returns: List[BCmd]): List[BCmd] = j match {
    case d: DirectCall =>
      val call = coerceProcedureCall(d.target)
      val returnTarget = d.returnTarget match {
        case Some(r) => List(GoToCmd(r.label))
        case None => List(Comment("no return target"), BAssume(FalseBLiteral))
      }
      d.condition match {
        case Some(c) =>
          val guard = c.toBoogie
          val guardGamma = c.toGamma
          List(BAssert(guardGamma), IfCmd(guard, call ++ returnTarget))
        case None =>
          call ++ returnTarget
      }
    case i: IndirectCall =>
      // TODO put this elsewhere
      val call: List[BCmd] = if (i.target.name == "R30") {
        returns :+ ReturnCmd
      } else {
        val unresolved: List[BCmd] = List(Comment(s"UNRESOLVED: call ${i.target.name}"), BAssume(FalseBLiteral))
        i.returnTarget match {
          case Some(r) => unresolved :+ GoToCmd(r.label)
          case None => unresolved ++ List(Comment("no return target"), BAssume(FalseBLiteral))
        }
      }
      i.condition match {
        case Some(c) =>
          val guard = c.toBoogie
          val guardGamma = c.toGamma
          List(BAssert(guardGamma), IfCmd(guard, call))
        case None =>
          call
      }
    case g: GoTo =>
      g.condition match {
        case Some(c) =>
          val guard = c.toBoogie
          val guardGamma = c.toGamma
          List(BAssert(guardGamma), IfCmd(guard, List(GoToCmd(g.target.label))))
        case None =>
          List(GoToCmd(g.target.label))
      }
  }

  def translate(s: Statement): List[BCmd] = s match {
    case m: MemoryAssign =>
      val lhs = m.lhs.toBoogie
      val rhs = m.rhs.toBoogie
      val lhsGamma = m.lhs.toGamma
      val rhsGamma = m.rhs.toGamma
      val store = AssignCmd(List(lhs, lhsGamma), List(rhs, rhsGamma))
      if (lhs == stack) {
        List(store)
      } else {
        val rely = ProcedureCall("rely", List(), List(), List(rhs.memory, rhsGamma.gammaMap))
        val gammaValueCheck = BAssert(BinaryBExpr(BoolIMPLIES, L(lhs, rhs.index), m.rhs.value.toGamma))
        val oldAssigns = guaranteeOldVars.map(g => AssignCmd(g.toOldVar, BMemoryLoad(lhs, g.toAddrVar, Endian.LittleEndian, g.size)))
        val oldGammaAssigns = controlled.map(g => AssignCmd(g.toOldGamma, BinaryBExpr(BoolOR, GammaLoad(lhsGamma, g.toAddrVar, g.size, g.size / m.lhs.valueSize), L(lhs, g.toAddrVar))))
        val secureUpdate = for (c <- controls.keys) yield {
          val addrCheck = BinaryBExpr(BVEQ, rhs.index, c.toAddrVar)
          val checks = controls(c).map(v => BinaryBExpr(BoolIMPLIES, L(lhs, v.toAddrVar), v.toOldGamma)).toList
          val checksAnd = if (checks.size > 1) {
            checks.tail.foldLeft(checks.head)((next: BExpr, ands: BExpr) => BinaryBExpr(BoolAND, next, ands))
          } else {
            checks.head
          }
          BAssert(BinaryBExpr(BoolIMPLIES, addrCheck, checksAnd))
        }
        val guaranteeChecks = guarantees.map(v => BAssert(v))
        (List(rely, gammaValueCheck) ++ oldAssigns ++ oldGammaAssigns :+ store) ++ secureUpdate ++ guaranteeChecks
      }
    case l: LocalAssign =>
      val lhs = l.lhs.toBoogie
      val rhs = l.rhs.toBoogie
      val lhsGamma = l.lhs.toGamma
      val rhsGamma = l.rhs.toGamma
      val assign = AssignCmd(List(lhs, lhsGamma), List(rhs, rhsGamma))
      val loads = rhs.functionOps.collect { case m: BMemoryLoad => m }
      if (loads.isEmpty || loads.forall(_.memory == stack)) {
        List(assign)
      } else {
        val gammas = rhsGamma.functionOps.collect { case g: GammaLoad => g.gammaMap }.toSeq.sorted
        val memories = loads.map(m => m.memory).toSeq.sorted
        List(ProcedureCall("rely", Seq(), Seq(), memories ++ gammas), assign)
      }
    case a: Assert =>
      val body = a.body.toBoogie
      List(BAssert(body, a.comment))
  }

  def coerceProcedureCall(target: Procedure): List[BCmd] = {
    val params = for (i <- target.in) yield {
      val register = i.value.toBoogie
      val registerGamma = i.value.toGamma
      if (i.value.size > i.size) {
        List(BVExtract(i.size, 0, register), registerGamma)
      } else if (i.value.size < i.size) {
        List(BVZeroExtend(i.size - i.value.size, register), registerGamma)
      } else {
        List(register, registerGamma)
      }
    }
    var outUsedRegisters: Set[Variable] = Set()
    var outIndices: Set[Int] = Set()
    for (o <- target.out.indices) {
      if (!outUsedRegisters.contains(target.out(o).value)) {
        outIndices = outIndices + o
        outUsedRegisters = outUsedRegisters + target.out(o).value
      }
    }

    val outTemp = for (o <- target.out.indices) yield {
      BVariable(s"#temp$o", BitVecBType(target.out(o).size), Scope.Local)
    }
    val outTempGamma = for (o <- target.out.indices) yield {
      BVariable(s"Gamma_#temp$o", BoolBType, Scope.Local)
    }
    val outRegisters = target.out.map(o => o.value.toBoogie)
    val outRegisterGammas = target.out.map(o => o.value.toGamma)
    val outAssigned = for (o <- target.out.indices if target.out(o).value.size != target.out(o).size && outIndices.contains(o)) yield {
      val regSize = target.out(o).value.size
      val paramSize = target.out(o).size
      if (regSize > paramSize) {
        AssignCmd(List(outRegisters(o), outRegisterGammas(o)), List(BVZeroExtend(regSize - paramSize, outTemp(o)), outTempGamma(o)))
      } else {
        AssignCmd(List(outRegisters(o), outRegisterGammas(o)), List(BVExtract(regSize, 0, outTemp(o)), outTempGamma(o)))
      }
    }

    val returned = for (o <- target.out.indices if outIndices.contains(o)) yield {
      if (target.out(o).value.size == target.out(o).size) {
        List(outRegisters(o), outRegisterGammas(o))
      } else {
        List(outTemp(o), outTempGamma(o))
      }
    }
    List(ProcedureCall(target.name, returned.flatten.toList, params.flatten.toList, List())) ++ outAssigned
  }

  /*
  private val reserved = Set("free")

  def avoidReserved(program: BProgram): BProgram = {
    program.replaceReserved(reserved)
  }
  */

}
