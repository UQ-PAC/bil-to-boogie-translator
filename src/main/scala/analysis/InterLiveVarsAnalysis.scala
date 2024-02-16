package analysis

import analysis.solvers.BackwardIDESolver
import ir.{Assert, Assume, GoTo, CFGPosition, Command, DirectCall, IndirectCall, LocalAssign, MemoryAssign, Procedure, Program, Variable, toShortString}

/**
 * Micro-transfer-functions for LiveVar analysis
 * this analysis works by inlining function calls (instead of just mapping parameters and returns all
 * live variables (registers) are propagated to and from callee functions)
 * The result of what variables are alive at each point in the program should still be correct
 * However, the functions that are callees of other functions will have an over approximation of their parameters
 * alive at the top of the function
 * Tip SPA IDE Slides include a short and clear explanation of microfunctions
 * https://cs.au.dk/~amoeller/spa/8-distributive.pdf
 */
trait LiveVarsAnalysisFunctions extends BackwardIDEAnalysis[Variable, FlatElement[Nothing] ,TwoElementLattice] {

  val valuelattice: TwoElementLattice = TwoElementLattice()
  val edgelattice: EdgeFunctionLattice[FlatElement[Nothing], valuelattice.type] = new EdgeFunctionLattice[FlatElement[Nothing], valuelattice.type](valuelattice)
  import edgelattice.{IdEdge, ConstEdge}

  def edgesCallToEntry(call: GoTo, entry: Command)(d: DL): Map[DL, edgelattice.Element] = {
    Map(d -> IdEdge())
  }

  def edgesExitToAfterCall(exit: Procedure, aftercall: DirectCall)(d: DL): Map[DL, edgelattice.Element] = {
    Map(d -> IdEdge())
  }

  def edgesCallToAfterCall(call: GoTo, aftercall: DirectCall)(d: DL): Map[DL, edgelattice.Element] = {
    d match
      case Left(value) => Map() // maps all variables before the call to bottom
      case Right(_) => Map(d -> IdEdge())
  }

  def edgesOther(n: CFGPosition)(d: DL): Map[DL, edgelattice.Element] = {
    n match
      case LocalAssign(variable, expr, maybeString) => // (s - variable) ++ expr.variables
        d match
          case Left(value) =>
            if value == variable then
              Map()
            else
              Map(d -> IdEdge())

          case Right(_) => expr.variables.foldLeft(Map(d -> IdEdge()): Map[DL, edgelattice.Element]) {
            (mp, expVar) => mp + (Left(expVar) -> ConstEdge(Top))
          }

      case MemoryAssign(memory, store, maybeString) => // s ++ store.index.variables ++ store.value.variables
        d match
          case Left(value) => Map(d -> IdEdge())
          case Right(_) =>
            (store.index.variables ++ store.value.variables).foldLeft(Map(d -> IdEdge()) : Map[DL, edgelattice.Element]) {
              (mp, storVar) => mp + (Left(storVar) -> ConstEdge(Top))
            }

      case Assume(expr, maybeString, maybeString1, bool) => // s ++ expr.variables
        d match
          case Left(value) => Map(d -> IdEdge())
          case Right(_) =>
            expr.variables.foldLeft(Map(d -> IdEdge()): Map[DL, edgelattice.Element]) {
              (mp, expVar) => mp + (Left(expVar) -> ConstEdge(Top))
            }

      case Assert(expr, maybeString, maybeString1) => // s ++ expr.variables
        d match
          case Left(value) => Map(d -> IdEdge())
          case Right(_) =>
            expr.variables.foldLeft(Map(d -> IdEdge()): Map[DL, edgelattice.Element]) {
              (mp, expVar) => mp + (Left(expVar) -> ConstEdge(Top))
            }
      case IndirectCall(variable, maybeBlock, maybeString) =>
        d match
          case Left(value) => if value != variable then Map(d -> IdEdge()) else Map()
          case Right(_) => Map(d -> IdEdge(), Left(variable) -> ConstEdge(Top))
      case _ => Map(d -> IdEdge())


  }
}

class InterLiveVarsAnalysis(program: Program)
  extends BackwardIDESolver[Variable, FlatElement[Nothing] ,TwoElementLattice](program), LiveVarsAnalysisFunctions


object InterLiveVarsAnalysis extends AnalysisResult[Map[CFGPosition, Map[Variable, FlatElement[Nothing]]]] {

  def encodeAnalysisResults(result: Map[CFGPosition, Map[Variable, FlatElement[Nothing]]]): String = {
    val pp = result.foldLeft("") {
      (m, f) =>
        val cfgPosition: CFGPosition = f._1
        val mapping: Map[Variable, FlatElement[Nothing]] = f._2
        val positionMaps = mapping.foldLeft("") {
          (line, pair) =>
            line + s"${pair._1}->${pair._2}<>"
        }

        m + s"${cfgPosition.toShortString}==>${positionMaps.dropRight(2)}\n"
    }
    pp.dropRight(1)
  }

  def parseAnalysisResults(input: String): String = {
    input.split("\n").sorted.foldLeft(Map(): Map[String, Set[String]]) {
      (m, line) =>
        val cfgPosition: String = line.split("==>", 2)(0)
        val rest: String = line.split("==>", 2)(1)
        m + (cfgPosition -> rest.split("<>").sorted.toSet)
    }.toString
  }
}



