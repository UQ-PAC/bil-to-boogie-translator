package analysis
import ir.*
import util.Logger

import scala.collection.mutable.ListBuffer

/** Evaluate an expression in a hope of finding a global variable.
  *
  * @param exp
  *   : The expression to evaluate (e.g. R1 + 0x1234)
  * @param n
  *   : The node where the expression is evaluated (e.g. mem[R1 + 0x1234] <- ...)
  * @return:
  *   The evaluated expression (e.g. 0x69632)
  */
def evaluateExpression(exp: Expr, constantPropResult: Map[Variable, FlatElement[BitVecLiteral]]): Option[BitVecLiteral] = {
  Logger.debug(s"evaluateExpression: $exp")
  exp match {
    case binOp: BinaryExpr =>
      val lhs = evaluateExpression(binOp.arg1, constantPropResult)
      val rhs = evaluateExpression(binOp.arg2, constantPropResult)

      (lhs, rhs) match {
        case (Some(l: BitVecLiteral), Some(r: BitVecLiteral)) =>
          binOp.op match {
            case BVADD => Some(BitVectorEval.smt_bvadd(l, r))
            case BVSUB => Some(BitVectorEval.smt_bvsub(l, r))
            case BVASHR => Some(BitVectorEval.smt_bvashr(l, r))
            case BVCOMP => Some(BitVectorEval.smt_bvcomp(l, r))
            case BVCONCAT => Some(BitVectorEval.smt_concat(l, r))
            case x =>
              Logger.error("Binary operation support not implemented: " + binOp.op)
              None
          }
        case _ => None
      }
    case extend: ZeroExtend =>
      evaluateExpression(extend.body, constantPropResult) match {
        case Some(b: BitVecLiteral) => Some(BitVectorEval.smt_zero_extend(extend.extension, b))
        case None                => None
      }
    case e: Extract =>
      evaluateExpression(e.body, constantPropResult) match {
        case Some(b: BitVecLiteral) => Some(BitVectorEval.boogie_extract(e.end, e.start, b))
        case None               => None
      }
    case variable: Variable =>
      constantPropResult(variable) match {
        case FlatEl(value) => Some(value)
        case Top           => None
        case Bottom           => None
      }
    case b: BitVecLiteral => Some(b)
    case _ => //throw new RuntimeException("ERROR: CASE NOT HANDLED: " + exp + "\n")
      None
  }
}

def evaluateExpressionWithSSA(exp: Expr, constantPropResult: Map[RegisterVariableWrapper, Set[BitVecLiteral]]): Set[BitVecLiteral] = {
  Logger.info(s"evaluateExpression: $exp")

  def apply(op: (BitVecLiteral, BitVecLiteral) => BitVecLiteral, a: Set[BitVecLiteral], b: Set[BitVecLiteral]): Set[BitVecLiteral] =
    val res = for {
      x <- a
      y <- b
    } yield op(x, y)
    res

  def applySingle(op: BitVecLiteral => BitVecLiteral, a: Set[BitVecLiteral]): Set[BitVecLiteral] =
    val res = for {
      x <- a
    } yield op(x)
    res


  exp match {
    case binOp: BinaryExpr =>
      val lhs = evaluateExpressionWithSSA(binOp.arg1, constantPropResult)
      val rhs = evaluateExpressionWithSSA(binOp.arg2, constantPropResult)

      (lhs, rhs) match {
        case (l: Set[BitVecLiteral], r: Set[BitVecLiteral]) =>
          binOp.op match {
            case BVADD => apply(BitVectorEval.smt_bvadd, lhs, rhs)
            case BVSUB => apply(BitVectorEval.smt_bvsub, lhs, rhs)
            case BVASHR => apply(BitVectorEval.smt_bvashr, lhs, rhs)
            case BVCOMP => apply(BitVectorEval.smt_bvcomp, lhs, rhs)
            case BVCONCAT => apply(BitVectorEval.smt_concat, lhs, rhs)
            case BVLSHR => apply(BitVectorEval.smt_bvlshr, lhs, rhs)
            case BVSHL => apply(BitVectorEval.smt_bvshl, lhs, rhs)
            case BVOR => apply(BitVectorEval.smt_bvor, lhs, rhs)
            case _ => throw new RuntimeException("Binary operation support not implemented: " + binOp.op)
          }
      }
    case extend: ZeroExtend =>
      val result = evaluateExpressionWithSSA(extend.body, constantPropResult)
      applySingle(BitVectorEval.smt_zero_extend(extend.extension, _: BitVecLiteral), result)
    case e: Extract =>
      val result = evaluateExpressionWithSSA(e.body, constantPropResult)
      applySingle(BitVectorEval.boogie_extract(e.end, e.start, _: BitVecLiteral), result)
    case variable: Variable =>
      val registerVariableWrapper = RegisterVariableWrapper(variable)
      constantPropResult.collect({
        case (k, v) if k == registerVariableWrapper => v
      }).flatten.toSet
      constantPropResult(registerVariableWrapper)
    case b: BitVecLiteral => Set(b)
    case _ => //throw new RuntimeException("ERROR: CASE NOT HANDLED: " + exp + "\n")
      Set()
  }
}

def unwrapExpr(expr: Expr): ListBuffer[Expr] = {
  val buffers = ListBuffer[Expr]()
  expr match {
    case e: Extract => unwrapExpr(e.body)
    case e: SignExtend => unwrapExpr(e.body)
    case e: ZeroExtend => unwrapExpr(e.body)
    case repeat: Repeat => unwrapExpr(repeat.body)
    case unaryExpr: UnaryExpr => unwrapExpr(unaryExpr.arg)
    case binaryExpr: BinaryExpr =>
      unwrapExpr(binaryExpr.arg1)
      unwrapExpr(binaryExpr.arg2)
    case memoryLoad: MemoryLoad =>
      buffers.addOne(memoryLoad)
      unwrapExpr(memoryLoad.index)
    case _ =>
  }
  buffers
}