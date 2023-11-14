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

  def visitAssume(node: Assume): Statement = {
    node.body = visitExpr(node.body)
    node
  }

  def visitAssert(node: Assert): Statement = {
    node.body = visitExpr(node.body)
    node
  }

  def visitJump(node: Jump): Jump = node.acceptVisit(this)

  def visitGoTo(node: GoTo): Jump = {
    node
  }

  def visitDirectCall(node: DirectCall): Jump = {
    node
  }

  def visitIndirectCall(node: IndirectCall): Jump = {
    node.target = visitVariable(node.target)
    node
  }

  def visitBlock(node: Block): Block = {
    for (i <- node.statements.indices) {
      node.statements(i) = visitStatement(node.statements(i))
    }
    node.jump = visitJump(node.jump)
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
    node.value = visitRegister(node.value)
    node
  }

  def visitProgram(node: Program): Program = {
    for (i <- node.procedures.indices) {
      val updatedProcedure = visitProcedure(node.procedures(i))
      val targetProcedure = node.procedures(i)
      if (targetProcedure == node.mainProcedure) {
        node.mainProcedure = updatedProcedure
      }
      node.procedures(i) = updatedProcedure
    }
    node
  }

  def visitExtract(node: Extract): Expr = {
    node.copy(body = visitExpr(node.body))
  }

  def visitRepeat(node: Repeat): Expr = {
    node.copy(body = visitExpr(node.body))
  }

  def visitZeroExtend(node: ZeroExtend): Expr = {
    node.copy(body = visitExpr(node.body))
  }

  def visitSignExtend(node: SignExtend): Expr = {
    node.copy(body = visitExpr(node.body))
  }

  def visitUnaryExpr(node: UnaryExpr): Expr = {
    node.copy(arg = visitExpr(node.arg))
  }

  def visitBinaryExpr(node: BinaryExpr): Expr = {
    node.copy(arg1 = visitExpr(node.arg1), arg2 = visitExpr(node.arg2))
  }

  def visitMemoryStore(node: MemoryStore): MemoryStore = {
    node.copy(mem = visitMemory(node.mem), index = visitExpr(node.index), value = visitExpr(node.value))
  }

  def visitMemoryLoad(node: MemoryLoad): Expr = {
    node.copy(mem = visitMemory(node.mem), index = visitExpr(node.index))
  }

  def visitMemory(node: Memory): Memory = node

  def visitVariable(node: Variable): Variable = node.acceptVisit(this)

  def visitRegister(node: Register): Register = node

  def visitLocalVar(node: LocalVar): LocalVar = node

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

  override def visitAssume(node: Assume): Statement = {
    visitExpr(node.body)
    node
  }

  override def visitAssert(node: Assert): Statement = {
    visitExpr(node.body)
    node
  }

  override def visitGoTo(node: GoTo): Jump = {
    node
  }

  override def visitDirectCall(node: DirectCall): Jump = {
    node
  }

  override def visitIndirectCall(node: IndirectCall): Jump = {
    visitVariable(node.target)
    node
  }

  override def visitBlock(node: Block): Block = {
    for (i <- node.statements) {
      visitStatement(i)
    }
    visitJump(node.jump)
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
    visitRegister(node.value)
    node
  }

  override def visitProgram(node: Program): Program = {
    for (i <- node.procedures) {
      visitProcedure(i)
    }
    node
  }

}

class StackSubstituter extends Visitor {
  val stackRefs: mutable.Set[Variable] = mutable.Set()
  val stackMemory: Memory = Memory("stack", 64, 8)

  override def visitMemoryLoad(node: MemoryLoad): MemoryLoad = {
    val loadStackRefs = node.index.variables.intersect(stackRefs)
    if (loadStackRefs.nonEmpty) {
      node.copy(mem = stackMemory)
    } else {
      node
    }
  }

}

class Substituter(variables: Map[Variable, Variable] = Map(), memories: Map[Memory, Memory] = Map()) extends Visitor {
  override def visitVariable(node: Variable): Variable = variables.get(node) match {
    case Some(v: Variable) => v
    case None              => node
  }

  override def visitMemory(node: Memory): Memory = memories.get(node) match {
    case Some(m: Memory) => m
    case None            => node
  }
}

/**
  * Prevents strings in 'reserved' from being used as the name of anything by adding a '#' to the start.
  * Useful for avoiding Boogie's reserved keywords.
  */
class Renamer(reserved: Set[String]) extends Visitor {
  override def visitLocalVar(node: LocalVar): LocalVar = {
    if (reserved.contains(node.name)) {
      node.copy(name = s"#${node.name}")
    } else {
      node
    }
  }

  override def visitMemory(node: Memory): Memory = {
    if (reserved.contains(node.name)) {
      node.copy(name = s"#${node.name}")
    } else {
      node
    }
  }

  override def visitParameter(node: Parameter): Parameter = {
    if (reserved.contains(node.name)) {
      node.name = s"#${node.name}"
    }
    super.visitParameter(node)
  }

  override def visitProcedure(node: Procedure): Procedure = {
    if (reserved.contains(node.name)) {
      node.name = s"#${node.name}"
    }
    super.visitProcedure(node)
  }

}

class ExternalRemover(external: Set[String]) extends Visitor {
  override def visitProcedure(node: Procedure): Procedure = {
    if (external.contains(node.name)) {
      // update the modifies set before removing the body
      node.modifies.addAll(node.blocks.flatMap(_.modifies))
      node.blocks = ArrayBuffer()
    }
    super.visitProcedure(node)
  }
}

/** Gives variables that are not contained within a MemoryStore or MemoryLoad
  * */
class VariablesWithoutStoresLoads extends ReadOnlyVisitor {
  val variables: mutable.Set[Variable] = mutable.Set()

  override def visitRegister(node: Register): Register = {
    variables.add(node)
    node
  }
  override def visitLocalVar(node: LocalVar): LocalVar = {
    variables.add(node)
    node
  }

  override def visitMemoryStore(node: MemoryStore): MemoryStore = {
    node
  }

  override def visitMemoryLoad(node: MemoryLoad): MemoryLoad = {
    node
  }

}
