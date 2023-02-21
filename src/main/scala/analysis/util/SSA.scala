package analysis.util

import analysis._
import astnodes.*
import analysis.solvers.*

import scala.collection.mutable
import scala.collection.mutable.HashMap
import scala.collection.mutable.ListBuffer

//Static Single Assignment (SSA) form
//Takes a program and normalises it based on that from

class SSA(cfg: Cfg) {
    val variableTracker: mutable.Map[String, Int] = mutable.HashMap()

    def analyze(): Unit =
    // generate the constraints by traversing the AST and solve them on-the-fly
      visit(cfg, ())
      post_SSA(cfg)

    def checkAssignment(name: String): Int = {
        if (variableTracker.contains(name)) {
            variableTracker(name) += 1
        } else {
            variableTracker(name) = 1
        }
        variableTracker(name)
    }

    def checkUse(name: String): Int = {
        if (!variableTracker.contains(name)) {
            variableTracker(name) = 1
        }
        variableTracker(name)
    }

    def visit(node: Object, arg: Unit): Unit = {
        node match {
            case localAssign: LocalAssign =>
                //localAssign.lhs = LocalVar(s"${localAssign.lhs.name}_${checkAssignment(localAssign.lhs.name)}", localAssign.lhs.size)
                localAssign.lhs.setSSA(checkAssignment(localAssign.lhs.toString))
                localAssign.rhs.setSSA(checkUse(localAssign.rhs.toString))
            case memAssign: MemAssign =>
//                memAssign.rhs = Store(memAssign.rhs.memory, s"${memAssign.rhs.index}_${checkAssignment(memAssign.rhs.index.toString)}", value, memAssign.rhs.endian, memAssign.rhs.size)
                  memAssign.rhs.index.setSSA(checkAssignment(memAssign.rhs.index.toString))
                  memAssign.rhs.value.setSSA(checkUse(memAssign.rhs.value.toString))
            case _ =>
        }
        visitChildren(node, ())
    }

//    def replacer(node: Object): Unit = {
//        node match {
//            case localAssign: LocalAssign =>
//                val newVar = LocalVar(s"${localAssign.lhs.name}_${checkAssignment(localAssign.lhs.name)}", localAssign.lhs.size)
//                val newExpr = localAssign.rhs match {
//                    case expr: Expr =>
//                        expr match {
//                            case binExpr: BinOp =>
//                                val newLeft = binExpr.lhs match {
//                                    case local: LocalVar => LocalVar(s"${local.name}_${checkUse(local.name)}", local.size)
//                                    case _ => binExpr.lhs
//                                }
//                                val newRight = binExpr.rhs match {
//                                    case local: LocalVar => LocalVar(s"${local.name}_${checkUse(local.name)}", local.size)
//                                    case _ => binExpr.rhs
//                                }
//                                BinOp(newLeft, binExpr.op, newRight)
//                            case unExpr: UnOp =>
//                              val newRight = unExpr.expr match {
//                                case local: LocalVar => LocalVar(s"${local.name}_${checkUse(local.name)}", local.size)
//                                case _ => unExpr.expr
//                              }
//                        }
//                    case _ => localAssign.rhs
//                }
//                LocalAssign(newVar, newExpr, localAssign.line, localAssign.instruction)
//            case memAssign: MemAssign =>
//            case _ => node
//        }
//        visitChildren(node, ())
//
//      def exprChecker(node: Object): Expr = {
//        node match {
//            case binExpr: BinOp =>
//                BinOp(binExpr.operator, exprChecker(binExpr.lhs), exprChecker(binExpr.rhs))
//            case unExpr: UnOp =>
//                UnOp(unExpr.operator, exprChecker(unExpr.exp))
//            case store: Store =>
//                Store(exprChecker(store.memory))
//        }
//      }
//    }

    def visitChildren(node: Object, arg: Unit): Unit = {
        node match {
            case cfg: Cfg =>
              cfg.nodes.foreach(visit(_, ()))

            case node: CfgNode =>
              node match {
                case stmtNode: CfgStatementNode =>
                  visit(stmtNode.data, ())
                case _ =>
              }

            case program: Program =>
                program.functions.foreach(visit(_, ()))

            case function: Subroutine =>
                function.blocks.foreach(visit(_, ()))

            case block: Block =>
                block.statements.foreach(visit(_, ()))

            case _ => // ignore other kinds of nodes

        }
    }

    def post_SSA(cfg: Cfg): Unit = {
      cfg.nodes.foreach {
        case statementNode: CfgStatementNode =>
          resolve_phi(statementNode, cfg)
        case _ =>
      }
    }

    def get_incoming_edges(cfg: Cfg, node: CfgNode): ListBuffer[Edge] = {
      val incomingEdges: ListBuffer[Edge] = ListBuffer()
      for (e <- cfg.getEdges.toList) {
        if (e.getTo().equals(node)) {
          incomingEdges.addOne(e)
        }
      }
      incomingEdges
    }

    def resolve_phi(node: CfgNode, cfg: Cfg): Unit = {

      def add_map(map: mutable.Map[Expr, ListBuffer[Expr]], key: Expr, value: Expr): Unit = {
        if (map.contains(key)) {
          map(key) += value
        } else {
          map(key) = ListBuffer(value)
        }
      }

      val incomingEdges = get_incoming_edges(cfg, node)
      //val incomingMatches: ListBuffer[Statement] = ListBuffer()
      var incomingMatches: mutable.Map[Expr, ListBuffer[Expr]] = mutable.Map[Expr, ListBuffer[Expr]]()
      val incomingMatches2: mutable.Map[Expr, ListBuffer[Expr]] = mutable.Map[Expr, ListBuffer[Expr]]()
      for (e <- incomingEdges) {
        node match {
          case stmtNode: CfgStatementNode =>
            stmtNode.data match
              case memAssign: MemAssign =>
                memAssign.rhs.value.locals.foreach(l => {
                  e.getFrom() match {
                    case fromStmtNode: CfgStatementNode =>
                      fromStmtNode.data match
                        case memAssign2: MemAssign =>
                          if (memAssign2.rhs.index.locals.contains(l)) {
                            memAssign2.rhs.index.locals.foreach(l2 => {
                              if (l2.equals(l)) {
                                add_map(incomingMatches, l, l2)
                                add_map(incomingMatches2, memAssign.rhs.value, memAssign2.rhs.index)
                              }
                            })
                          }
                        case localAssign: LocalAssign =>
                          if (localAssign.lhs.locals.contains(l)) {
                            localAssign.lhs.locals.foreach(l2 => {
                              if (l2.equals(l)) {
                                add_map(incomingMatches, l, l2)
                                add_map(incomingMatches2, memAssign.rhs.value, localAssign.lhs)
                              }
                            })
                          }
                        case _ =>
                    case _ =>
                  }
                })
              case localAssign: LocalAssign =>
                localAssign.rhs.locals.foreach(l => {
                  e.getFrom() match {
                    case fromStmtNode: CfgStatementNode =>
                      fromStmtNode.data match
                        case memAssign: MemAssign =>
                          if (memAssign.rhs.index.locals.contains(l)) {
                            memAssign.rhs.index.locals.foreach(l2 => {
                              if (l2.equals(l)) {
                                add_map(incomingMatches, l, l2)
                                add_map(incomingMatches2, localAssign.rhs, memAssign.rhs.index)
                              }
                            })
                          }
                        case localAssign2: LocalAssign =>
                          if (localAssign2.lhs.locals.contains(l)) {
                            localAssign2.lhs.locals.foreach(l2 => {
                              if (l2.equals(l)) {
                                add_map(incomingMatches, l, l2)
                                add_map(incomingMatches2, localAssign.rhs, localAssign2.lhs)
                              }
                            })
                          }
                        case _ =>
                    case _ =>
                  }
                })
              case _ =>
          case _ =>
        }
      }


//      // for whole expression
//      for (e <- incomingEdges) {
//        node match {
//          case stmtNode: CfgStatementNode =>
//            stmtNode.data match
//              case memAssign: MemAssign =>
//                val l = memAssign.rhs.value
//                  e.getFrom() match {
//                    case fromStmtNode: CfgStatementNode =>
//                      fromStmtNode.data match
//                        case memAssign2: MemAssign =>
//                            val l2 = memAssign2.rhs.index
//                            if (l2.equals(l)) {
//                              add_map(incomingMatches, l, l2)
//                            }
//                        case localAssign: LocalAssign =>
//                            val l2 = localAssign.lhs
//                            if (l2.equals(l)) {
//                              add_map(incomingMatches, l, l2)
//                            }
//                        case _ =>
//                    case _ =>
//                  }
//              case localAssign: LocalAssign =>
//                val l = localAssign.rhs
//                  e.getFrom() match {
//                    case fromStmtNode: CfgStatementNode =>
//                      fromStmtNode.data match
//                        case memAssign: MemAssign =>
//                            val l2 = memAssign.rhs.index
//                            if (l2.equals(l)) {
//                              add_map(incomingMatches, l, l2)
//                            }
//                        case localAssign2: LocalAssign =>
//                            val l2 = localAssign2.lhs
//                            if (l2.equals(l)) {
//                              add_map(incomingMatches, l, l2)
//                            }
//                        case _ =>
//                    case _ =>
//                  }
//              case _ =>
//          case _ =>
//        }
//      }

      incomingMatches = incomingMatches.concat(incomingMatches2)

      // Flow corrector: replace phi with incoming edges
      // TODO: needs to be fixed cause it just selects the highest value of the incoming edges
      incomingMatches.foreach((key, value) =>
        if (value.length == 1) {
            // replace key with value
            key.setSSA(value.head.getSSA())
            } else if (value.length > 1) {
            // replace key with phi
            value.foreach(v =>
              if (v.getSSA() > key.getSSA()) {
                key.setSSA(v.getSSA())
              }
            )
            } else {
            // no incoming edges
        }
      )

//      incomingMatches2.foreach((key, value) =>
//        print(s"key: ($key, ${key.getSSA()}), value: ")
//        value.foreach(v => print(s"($v,${v.getSSA()})"))
//        println()
//      )

      incomingMatches.foreach((key, value) =>
        print(s"key: ($key, ${key.getSSA()}), value: ")
        value.foreach(v => print(s"($v,${v.getSSA()})"))
        println()
      )
    }


//    def resolve_phi_rec(node: CfgNode, cfg: Cfg): mutable.Map[Expr, ListBuffer[Expr]] = {
//
//      def add_map(map: mutable.Map[Expr, ListBuffer[Expr]], key: Expr, value: Expr): Unit = {
//        if (map.contains(key)) {
//          map(key) += value
//        } else {
//          map(key) = ListBuffer(value)
//        }
//      }
//
//      val incomingEdges = get_incoming_edges(cfg, node)
//      val incomingMatches: mutable.Map[Expr, ListBuffer[Expr]] = mutable.Map[Expr, ListBuffer[Expr]]()
//      val incomingMatches2: mutable.Map[Expr, ListBuffer[Expr]] = mutable.Map[Expr, ListBuffer[Expr]]()
//
//      for (e <- incomingEdges) {
//        node match {
//          case stmtNode: CfgStatementNode =>
//            stmtNode.data match
//              case memAssign: MemAssign =>
//                memAssign.rhs.value.locals.foreach(l => {
//                  e.getFrom() match {
//                    case fromStmtNode: CfgStatementNode =>
//                      fromStmtNode.data match
//                        case memAssign2: MemAssign =>
//                          if (memAssign2.rhs.index.locals.contains(l)) {
//                            memAssign2.rhs.index.locals.foreach(l2 => {
//                              if (l2.equals(l)) {
//                                add_map(incomingMatches, l, l2)
//                                add_map(incomingMatches2, memAssign.rhs.value, memAssign2.rhs.index)
//                              }
//                            })
//                          }
//                        case localAssign: LocalAssign =>
//                          if (localAssign.lhs.locals.contains(l)) {
//                            localAssign.lhs.locals.foreach(l2 => {
//                              if (l2.equals(l)) {
//                                add_map(incomingMatches, l, l2)
//                                add_map(incomingMatches2, memAssign.rhs.value, localAssign.lhs)
//                              }
//                            })
//                          }
//                        case _ =>
//                    case _ =>
//                  }
//                })
//              case localAssign: LocalAssign =>
//                localAssign.rhs.locals.foreach(l => {
//                  e.getFrom() match {
//                    case fromStmtNode: CfgStatementNode =>
//                      fromStmtNode.data match
//                        case memAssign: MemAssign =>
//                          if (memAssign.rhs.index.locals.contains(l)) {
//                            memAssign.rhs.index.locals.foreach(l2 => {
//                              if (l2.equals(l)) {
//                                add_map(incomingMatches, l, l2)
//                                add_map(incomingMatches2, localAssign.rhs, memAssign.rhs.index)
//                              }
//                            })
//                          }
//                        case localAssign2: LocalAssign =>
//                          if (localAssign2.lhs.locals.contains(l)) {
//                            localAssign2.lhs.locals.foreach(l2 => {
//                              if (l2.equals(l)) {
//                                add_map(incomingMatches, l, l2)
//                                add_map(incomingMatches2, localAssign.rhs, localAssign2.lhs)
//                              }
//                            })
//                          }
//                        case _ =>
//                    case _ =>
//                  }
//                })
//              case _ =>
//          case _ =>
//        }
//      }
//      incomingMatches
//    }
}