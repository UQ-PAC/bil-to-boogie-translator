package analysis;

import vcgen.*;
import astnodes.stmt.*;
import scala.collection.mutable.ArrayDeque;
import java.lang.NullPointerException;

class Worklist(val analysis: AnalysisPoint, startState: State) {
    private final val debug: Boolean = false;
    private val directionForwards: Boolean = analysis.isForwards;
    private val libraryFunctions: Set[String] = analysis.libraryFunctions;

    var currentCallString: Set[String] = Set();
    var currentWorklist: ArrayDeque[Block] = ArrayDeque();

    var previousStmtAnalysisState: analysis.type = analysis.createLowest;
    var finalStmtAnalysisState: analysis.type = analysis.createLowest;
    var stmtAnalysisInfo: Map[Stmt, analysis.type] = Map();
    var blockAnalysisInfo: Map[Block, analysis.type] = Map();
    
    def getAllInfo: Map[Stmt, analysis.type] = {
        stmtAnalysisInfo;
    }

    def getOneInfo(stmt: Stmt): analysis.type = {
        stmtAnalysisInfo.getOrElse(stmt, analysis.createLowest);
    }

    def doAnalysis: State = {
        printAllLinesWithLabels
        analyseFunction("main");
        if debug then println(getAllInfo);

        // finalStmtAnalysisState.asInstanceOf[ConstantPropagationAnalysis].debugPrint()
        previousStmtAnalysisState = null;
        blockAnalysisInfo = null;

        finalStmtAnalysisState.applyChanges(startState, getAllInfo);
    }
    
    def printAllLinesWithLabels: Unit = {
        startState.functions.foreach(function =>
            {function.labelToBlock.values.foreach(block => {
                block.lines.foreach(line => {
                    println(line.label.pc + " : " + line)
                })
            })})
    }
    
    // def printAllStates: Unit = {
    //     finalAnalysedStmtInfo.foreach(point => {
    //         println("Line:")
    //         System.out.println(point._1.getLabel.pc + " " + point._1)
    //         println("Dependencies:")
    //         point._2.asInstanceOf[ConstantPropagationAnalysis].state.foreach(varConstraint => {
    //             System.out.println(varConstraint._1.toString + " : " + varConstraint._2)
    //         })
    //     })
    // }

    def analyseFunction(name: String) = {
        if debug then println("analysing function: " + name);

        currentCallString = currentCallString + name;
        currentWorklist = findFunctionRootBlock(name);

        var functionStartAnalysisState: analysis.type = previousStmtAnalysisState;
        var currentFunctionAnalysedInfo: Map[Stmt, analysis.type] = Map();

        while (!currentWorklist.isEmpty) {
            var nextBlockToAnalyse: Block = currentWorklist.removeHead();

            if (!getBlockParents(nextBlockToAnalyse).isEmpty) {
                getBlockParents(nextBlockToAnalyse).foreach(block => {
                    previousStmtAnalysisState = previousStmtAnalysisState.combine(blockAnalysisInfo.getOrElse(block, analysis.createLowest))
                });
            } else {
                previousStmtAnalysisState = analysis.createLowest;
            }

            // println("BEFORE")
            // currentFunctionAnalysedInfo.foreach(newAnalysisPoint => {
            //     println(newAnalysisPoint._1)
            //     newAnalysisPoint._2.asInstanceOf[ConstantPropagationAnalysis].debugPrint()
            // })

            currentFunctionAnalysedInfo = analyseBlock(nextBlockToAnalyse, currentFunctionAnalysedInfo);

            // println("AFTER")
            // currentFunctionAnalysedInfo.foreach(newAnalysisPoint => {
            //     println(newAnalysisPoint._1)
            //     newAnalysisPoint._2.asInstanceOf[ConstantPropagationAnalysis].debugPrint()
            // })

            if (!currentWorklist.isEmpty) {
                previousStmtAnalysisState = functionStartAnalysisState;
            }

            finalStmtAnalysisState = previousStmtAnalysisState
            // previousStmtAnalysisState.asInstanceOf[ConstantPropagationAnalysis].debugPrint()
        }

        // println("END")
        // currentFunctionAnalysedInfo.foreach(newAnalysisPoint => {
        //     println(newAnalysisPoint._1)
        //     newAnalysisPoint._2.asInstanceOf[ConstantPropagationAnalysis].debugPrint()
        // })
        saveNewAnalysisInfo(currentFunctionAnalysedInfo);
        currentCallString = currentCallString.filter(funcName => {funcName != name});
    }

    def analyseBlock(block: Block, currentInfo: Map[Stmt, analysis.type]): Map[Stmt, analysis.type] = {
        if debug then println("analysing block: " + block.label);
        var outputInfo: Map[Stmt, analysis.type] = currentInfo;

        block.lines.foreach(blockStmt => {
            outputInfo = analyseStmt(blockStmt, outputInfo);
        })
        
        if (blockAnalysisInfo.getOrElse(block, null) != previousStmtAnalysisState) {
            blockAnalysisInfo = blockAnalysisInfo + (block -> previousStmtAnalysisState);

            (getBlockChildren(block) + block).foreach(b => {
                if (!currentWorklist.contains(b)) {
                    currentWorklist.append(b);
                }
            })
        } else {
            ;
        }

        outputInfo;
    }

    def analyseStmt(stmt: Stmt, currentInfo: Map[Stmt, analysis.type]): Map[Stmt, analysis.type] = {
        if debug then println("analysing stmt: " + stmt);
        var outputInfo: Map[Stmt, analysis.type] = null;
        
        stmt match {
            case functionCallStmt: CallStmt => {
                var inProgressWorklist: ArrayDeque[Block] = currentWorklist;

                if (!currentCallString.contains(functionCallStmt.funcName)) {
                    previousStmtAnalysisState = previousStmtAnalysisState.transferAndCheck(stmt);

                    outputInfo = currentInfo + (stmt -> previousStmtAnalysisState);

                    if (!libraryFunctions.contains(functionCallStmt.funcName)) {
                        analyseFunction(functionCallStmt.funcName);
                    }
                } else {
                    println(currentCallString);
                    println("ignoring recursive call in " + functionCallStmt.funcName);
                }

                currentWorklist = inProgressWorklist;
            }
            case _ => {
                previousStmtAnalysisState = previousStmtAnalysisState.transferAndCheck(stmt);

                outputInfo  = currentInfo + (stmt -> previousStmtAnalysisState);
            }
        }

        outputInfo;
    }

    /**
     * The process for these two is similar:

     * Find the FunctionState that the block belongs to
     * Get the labels of its children/parents from that FunctionState
     * Map those labels to blocks, by:
     *  Finding the FunctionState that the label belongs to
     *  Getting the Block from that FunctionState
     */
    def getBlockChildren(block: Block): Set[Block] = {
        startState.functions.find((func: FunctionState) => {
            func.labelToBlock.contains(block.label)
        }).get.children(block).getOrElse(Set[String]()).map(label => {
            startState.functions.find((func: FunctionState) => {
                func.labelToBlock.contains(label)
            }).get.labelToBlock.get(label).getOrElse(null)
        })
    }

    def getBlockParents(block: Block): Set[Block] = {
        startState.functions.find((func: FunctionState) => {
            func.labelToBlock.contains(block.label)
        }).get.parents(block).map(label => {
            startState.functions.find((func: FunctionState) => {
                func.labelToBlock.contains(label)
            }).get.labelToBlock.get(label).getOrElse(null)
        }).toSet
    }

    /**
     * Finds the root block of a function given the function's name.
     */
    def findFunctionRootBlock(funcName: String): ArrayDeque[Block] = {
        ArrayDeque(
            startState.functions.find((func: FunctionState) => {
                func.header.getFuncName == funcName;
            }).get.rootBlock
        );
    }

    /**
     * "Commits" the info from the current function to the output map.
     */
    def saveNewAnalysisInfo(newInfo: Map[Stmt, analysis.type]) = {

        // newInfo.foreach(point => {
        //     println(point._1)
        //     point._2.asInstanceOf[ConstantPropagationAnalysis].debugPrint()
        // })

        // println("whole thing")
        // stmtAnalysisInfo.foreach(point => {
        //     println(point._1)
        //     point._2.asInstanceOf[ConstantPropagationAnalysis].debugPrint()
        // })

        println("SAVING INFO")
        newInfo.foreach(newAnalysisPoint => {
            println(newAnalysisPoint._1)
            newAnalysisPoint._2.asInstanceOf[ConstantPropagationAnalysis].debugPrint()
            stmtAnalysisInfo = stmtAnalysisInfo + (newAnalysisPoint._1 -> stmtAnalysisInfo.getOrElse(newAnalysisPoint._1, analysis.createLowest).asInstanceOf[analysis.type].join(newAnalysisPoint._2.asInstanceOf[analysis.type]))
        })
    }
}