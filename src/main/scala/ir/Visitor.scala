package ir

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable

abstract class Visitor {

  def visitExpr(node: Expr): Expr = node.acceptVisit(this)

  def visitStatement(node: Statement): Statement = node.acceptVisit(this)

  def visitLocalAssign(node: LocalAssign): Statement = {
    node.lhs = visitVariable(node.lhs)
    node.rhs = visitExpr(node.rhs)
    node
  }

  def visitMemoryAssign(node: MemoryAssign): Statement = {
    node.lhs = visitMemory(node.lhs)
    node.rhs = visitMemoryStore(node.rhs)
    node
  }

  def visitJump(node: Jump): Jump = node.acceptVisit(this)

  def visitGoTo(node: GoTo): Jump = {
    node.condition = node.condition.map(visitExpr)
    node
  }

  def visitDirectCall(node: DirectCall): Jump = {
    node.condition = node.condition.map(visitExpr)
    node
  }

  def visitIndirectCall(node: IndirectCall): Jump = {
    node.condition = node.condition.map(visitExpr)
    node.target = visitVariable(node.target)
    node
  }

  def visitBlock(node: Block): Block = {
    for (i <- node.statements.indices) {
      node.statements(i) = visitStatement(node.statements(i))
    }
    for (i <- node.jumps.indices) {
      node.jumps(i) = visitJump(node.jumps(i))
    }
    node
  }

  def visitProcedure(node: Procedure): Procedure = {
    for (i <- node.blocks.indices) {
      node.blocks(i) = visitBlock(node.blocks(i))
    }
    for (i <- node.in.indices) {
      node.in(i) = visitParameter(node.in(i))
    }
    for (i <- node.out.indices) {
      node.out(i) = visitParameter(node.out(i))
    }
    node
  }

  def visitParameter(node: Parameter): Parameter = {
    node.value = visitVariable(node.value)
    node
  }

  def visitProgram(node: Program): Program = {
    for (i <- node.procedures.indices) {
      node.procedures(i) = visitProcedure(node.procedures(i))
    }
    node
  }

  def visitExtract(node: Extract): Expr = {
    node.body = visitExpr(node.body)
    node
  }

  def visitRepeat(node: Repeat): Expr = {
    node.body = visitExpr(node.body)
    node
  }

  def visitZeroExtend(node: ZeroExtend): Expr = {
    node.body = visitExpr(node.body)
    node
  }

  def visitSignExtend(node: SignExtend): Expr = {
    node.body = visitExpr(node.body)
    node
  }

  def visitUnaryExpr(node: UnaryExpr): Expr = {
    node.arg = visitExpr(node.arg)
    node
  }

  def visitBinaryExpr(node: BinaryExpr): Expr = {
    node.arg1 = visitExpr(node.arg1)
    node.arg2 = visitExpr(node.arg2)
    node
  }

  def visitMemoryStore(node: MemoryStore): MemoryStore = {
    node.mem = visitMemory(node.mem)
    node.index = visitExpr(node.index)
    node.value = visitExpr(node.value)
    node
  }

  def visitMemoryLoad(node: MemoryLoad): Expr = {
    node.mem = visitMemory(node.mem)
    node.index = visitExpr(node.index)
    node
  }

  def visitMemory(node: Memory): Memory = node

  def visitVariable(node: Variable): Variable = node

  def visitLiteral(node: Literal): Literal = node

}

abstract class ReadOnlyVisitor extends Visitor {
  override def visitExtract(node: Extract): Expr = {
    visitExpr(node.body)
    node
  }

  override def visitRepeat(node: Repeat): Expr = {
    visitExpr(node.body)
    node
  }

  override def visitZeroExtend(node: ZeroExtend): Expr = {
    visitExpr(node.body)
    node
  }

  override def visitSignExtend(node: SignExtend): Expr = {
    visitExpr(node.body)
    node
  }

  override def visitUnaryExpr(node: UnaryExpr): Expr = {
    visitExpr(node.arg)
    node
  }

  override def visitBinaryExpr(node: BinaryExpr): Expr = {
    visitExpr(node.arg1)
    visitExpr(node.arg2)
    node
  }

  override def visitMemoryStore(node: MemoryStore): MemoryStore = {
    visitMemory(node.mem)
    visitExpr(node.index)
    visitExpr(node.value)
    node
  }

  override def visitMemoryLoad(node: MemoryLoad): Expr = {
    visitMemory(node.mem)
    visitExpr(node.index)
    node
  }

  override def visitLocalAssign(node: LocalAssign): Statement = {
    visitVariable(node.lhs)
    visitExpr(node.rhs)
    node
  }

  override def visitMemoryAssign(node: MemoryAssign): Statement = {
    visitMemory(node.lhs)
    visitMemoryStore(node.rhs)
    node
  }

  override def visitGoTo(node: GoTo): Jump = {
    node.condition.map(visitExpr)
    node
  }

  override def visitDirectCall(node: DirectCall): Jump = {
    node.condition.map(visitExpr)
    node
  }

  override def visitIndirectCall(node: IndirectCall): Jump = {
    node.condition.map(visitExpr)
    visitVariable(node.target)
    node
  }

  override def visitBlock(node: Block): Block = {
    for (i <- node.statements) {
      visitStatement(i)
    }
    for (i <- node.jumps) {
      visitJump(i)
    }
    node
  }

  override def visitProcedure(node: Procedure): Procedure = {
    for (i <- node.blocks) {
      visitBlock(i)
    }
    for (i <- node.in) {
      visitParameter(i)
    }
    for (i <- node.out) {
      visitParameter(i)
    }
    node
  }

  override def visitParameter(node: Parameter): Parameter = {
    visitVariable(node.value)
    node
  }

  override def visitProgram(node: Program): Program = {
    for (i <- node.procedures) {
      visitProcedure(i)
    }
    node
  }

}

abstract class ControlFlowInterproceduralVisitor extends Visitor {
  val visited: mutable.Set[Procedure] = mutable.Set()

  override def visitProcedure(node: Procedure): Procedure = {
    for (i <- node.blocks.indices) {
      node.blocks(i) = visitBlock(node.blocks(i))
    }
    for (i <- node.in.indices) {
      node.in(i) = visitParameter(node.in(i))
    }
    for (i <- node.out.indices) {
      node.out(i) = visitParameter(node.out(i))
    }
    node
  }

}

class Substituter(variables: Map[Variable, Variable] = Map(), memories: Map[Memory, Memory] = Map()) extends Visitor {
  override def visitVariable(node: Variable): Variable = variables.get(node) match {
    case Some(v: Variable) => v
    case None => node
  }

  override def visitMemory(node: Memory): Memory = memories.get(node) match {
    case Some(m: Memory) => m
    case None => node
  }
}

class Renamer(reserved: Set[String]) extends Visitor {
  override def visitVariable(node: Variable): Variable = {
    if (reserved.contains(node.name)) {
      node.copy(name = '#' + node.name)
    } else {
      node
    }
  }

  override def visitMemory(node: Memory): Memory = {
    if (reserved.contains(node.name)) {
      node.copy(name = '#' + node.name)
    } else {
      node
    }
  }

  override def visitParameter(node: Parameter): Parameter = {
    if (reserved.contains(node.name)) {
      node.name = '#' + node.name
    }
    super.visitParameter(node)
  }

  override def visitProcedure(node: Procedure): Procedure = {
    if (reserved.contains(node.name)) {
      node.name = '#' + node.name
    }
    super.visitProcedure(node)
  }

}

class ExternalRemover(external: Set[String]) extends Visitor {
  override def visitProcedure(node: Procedure): Procedure = {
    if (external.contains(node.name)) {
      node.blocks = ArrayBuffer()
    }
    super.visitProcedure(node)
  }
}

class TypeChecker extends Visitor {

}
