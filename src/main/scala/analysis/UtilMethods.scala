package analysis
import ir.*
import util.Logger

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
            case _ => throw new RuntimeException("Binary operation support not implemented: " + binOp.op)
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
  Logger.debug(s"evaluateExpression: $exp")

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
            case _ => throw new RuntimeException("Binary operation support not implemented: " + binOp.op)
          }
        case _ => Set()
      }
    case extend: ZeroExtend =>
      evaluateExpressionWithSSA(extend.body, constantPropResult) match {
        case b: Set[BitVecLiteral] if b.nonEmpty => applySingle(BitVectorEval.smt_zero_extend(extend.extension, _: BitVecLiteral), b)
        case _                => Set()
      }
    case e: Extract =>
      evaluateExpressionWithSSA(e.body, constantPropResult) match {
        case b: Set[BitVecLiteral] if b.nonEmpty => applySingle(BitVectorEval.boogie_extract(e.end, e.start, _: BitVecLiteral), b)
        case _               => Set()
      }
    case registerVariableWrapper: RegisterVariableWrapper =>
      constantPropResult(registerVariableWrapper)
    case b: BitVecLiteral => Set(b)
    case _ => //throw new RuntimeException("ERROR: CASE NOT HANDLED: " + exp + "\n")
      Set()
  }
}