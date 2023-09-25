package translating
import ir._


private class ILSerialiser extends ReadOnlyVisitor {
  var program: StringBuilder = StringBuilder()

  var indentLevel = 0

  def getIndent(): String = {
    "  " * indentLevel
  }

  def blockIdentifier(block: Block) : String = {
    val i = block.address match {
      case Some(addr) =>  f"${addr}:${block.label}"
      case None => f"?:${block.label}"
    }
    '"' + i + '"'
  }

  def procedureIdentifier(proc: Procedure): String = {
    val i = proc.address match {
      case Some(addr) =>  f"${addr}:${proc.name}"
      case None => f"?:${proc.name}"
    }
    '"' + i + '"'
  }


  override def visitExpr(node: Expr): Expr = {
    node.acceptVisit(this)
  }

  override def visitStatement(node: Statement): Statement = node.acceptVisit(this)

  override def visitLocalAssign(node: LocalAssign): Statement = {
    program ++= "LocalAssign("
    visitVariable(node.lhs)
    program ++= " := "
    visitExpr(node.rhs)
    program ++= ")"
    node
  }

  override def visitMemoryAssign(node: MemoryAssign): Statement = {
    program ++= "MemoryAssign("
    visitMemoryStore(node.rhs)
    program ++= ")"
    node
  }

  override def visitAssert(node: Assert): Statement = {
    program ++= "Assert("
    visitExpr(node.body)
    program ++= ")"
    node
  }

  override def visitJump(node: Jump): Jump = {
    node.acceptVisit(this)
    node
  }

  override def visitGoTo(node: GoTo): Jump = {
    program ++= "GoTo(" 
    // TODO 
    program ++= blockIdentifier(node.target)
    program ++= ", "
    program ++= "condition("
    node.condition.map(visitExpr)
    program ++= ")" // Condition
    program ++= ")" // GoTo
    node
  }

  override def visitDirectCall(node: DirectCall): Jump = {
    program ++= "DirectCall("
    program ++= procedureIdentifier(node.target)
    program ++= ", "
    program ++= "condition("
    node.condition.map(visitExpr)
    program ++= ")" // Condition
    program ++= ")" // DirectCall 
    node
  }

  override def visitIndirectCall(node: IndirectCall): Jump = {
    program ++= "IndirectCall("
    visitVariable(node.target)
    program ++= ", "
    program ++= "condition("
    node.condition.map(visitExpr)
    program ++= ")" // Condition
    program ++= ")" // IndirectCall 
    node
  }

  override def visitBlock(node: Block): Block = {
    program ++= getIndent()
    program ++= "Block(" + blockIdentifier(node) + ",\n"
    indentLevel += 1
    program ++= getIndent()
    program ++= "statements(\n"
    indentLevel += 1

    for (i <- node.statements.indices) {
      program ++= getIndent()
      visitStatement(node.statements(i))
      program ++= "\n"
    }
    indentLevel -= 1
    program ++= getIndent() + "),\n"
    program ++= getIndent() + "jumps(\n"
    indentLevel += 1
    for (j <- node.jumps) {
      program ++= getIndent()
      visitJump(j)
      program ++= "\n"
    }
    indentLevel -= 1
    program ++= getIndent() + ")\n"
    indentLevel -= 1
    program ++= getIndent()
    program ++= ")\n"
    node
  }

  override def visitProcedure(node: Procedure): Procedure = {
    program ++= "Procedure(" + procedureIdentifier(node) + ", "
    indentLevel += 1
  
      program ++= "in("
    for (i <- node.in.indices) {
      visitParameter(node.in(i))
      if (i != node.in.size - 1) {
        program ++= ", "
      }
    }
    program ++= "), "
    program ++= "out("
    for (i <- node.out.indices) {
      visitParameter(node.out(i))
      if (i != node.out.size - 1)
        program ++= ", "
    }
    program ++= "), "
    program ++= "blocks(\n"
    for (i <- node.blocks.indices) {
      visitBlock(node.blocks(i))
    }
    program ++= ")),\n"
    indentLevel -= 1
    node
  }

  override def visitParameter(node: Parameter): Parameter = {
    program ++= "Parameter("
    visitRegister(node.value)
    program ++= ")"
    node
  }

  override def visitProgram(node: Program): Program = {
    for (i <- node.procedures) {
      visitProcedure(i)
    }
    node
  }

  override def visitExtract(node: Extract): Expr = {
    program ++= "Extract("
    visitExpr(node.body)
    program ++= f"[${node.end}:${node.start}]"
    program ++= ")"
    node
  }

  override def visitRepeat(node: Repeat): Expr = {
    program ++= "Repeat("
    visitExpr(node.body)
    program ++= f", ${node.repeats}"
    program ++= ")"
    node
  }

  override def visitZeroExtend(node: ZeroExtend): Expr = {
    program ++= "ZeroExtend("
    visitExpr(node.body)
    program ++= f", ${node.extension}"
    program ++= ")"
    node
  }

  override def visitSignExtend(node: SignExtend): Expr = {
    program ++= "SignExtend("
    visitExpr(node.body)
    program ++= f", ${node.extension}"
    program ++= ")"
    node
  }

  override def visitUnaryExpr(node: UnaryExpr): Expr = {
    program ++= "UnaryExpr("
    program ++= '"' + f"${node.op}" + '"' + ", "
    visitExpr(node.arg)
    program ++= ")"
    node
  }

  override def visitBinaryExpr(node: BinaryExpr): Expr = {
    program ++= "BinaryExpr("
    program ++= "\"" + node.op + '"' + ", "
    visitExpr(node.arg1)
    program ++= ", "
    visitExpr(node.arg2)
    program ++= ")"
    node
  }

  override def visitMemoryStore(node: MemoryStore): MemoryStore = {
    program ++= "MemoryStore("
    visitMemory(node.mem)
    program ++= "["
    visitExpr(node.index)
    program ++= "] := "
    visitExpr(node.value)
    program ++= ")"
    node
  }

  override def visitMemoryLoad(node: MemoryLoad): Expr = {
    program ++= "MemoryLoad("
    visitMemory(node.mem)
    program ++= ", ["
    visitExpr(node.index)
    program ++= "])"
    node
  }

  override def visitMemory(node: Memory): Memory = {
    program ++= "Memory(" 
    program ++= '"' + node.name + '"'
    program ++= f", ${node.addressSize}, ${node.valueSize})"
    node
  }

  override def visitVariable(node: Variable): Variable = {
    program ++= node.toString()
    node
  }

  override def visitRegister(node: Register): Register = {
    program ++= node.toString()
    node
  }

  override def visitLocalVar(node: LocalVar): LocalVar = {
    program ++= node.toString()
    node
  }

  override def visitLiteral(node: Literal): Literal = {
    program ++= node.toString()
    node
  }


}

def serialiseIL(p: Program): String = {
  val s = ILSerialiser()
  s.visitProgram(p)
  s.program.toString()
}
