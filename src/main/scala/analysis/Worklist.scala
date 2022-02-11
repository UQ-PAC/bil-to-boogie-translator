package analysis;

import vcgen.*;
import astnodes.stmt.*;
import scala.collection.mutable.ArrayDeque;
import java.lang.NullPointerException;

/**
 * TODO & future work:
 *  Consider mixins - have a series of traits that define different analysis properties like path-sensitivity
 *  Consider replacing the entire worklist & analysis framework with a single analysis, i.e. VSA (see G. Balakrishnan)
 *  Consider parameterising the analysis with a generic? (questions: how to insantiate an analysis when you only have the type?)
 */
class Worklist(val analysis: AnalysisPoint, startState: State) {
    private final val debug: Boolean = true;
    private val directionForwards: Boolean = analysis.isForwards;

    var currentCallString: Set[String] = Set(); // call string to avoid recursion
    var currentWorklist: ArrayDeque[Block] = ArrayDeque(); // queue of blocks to work on per-function
    var previousStmtAnalysisState: analysis.type = analysis.createLowest; // previous analysisPoint info per-statement
    var stmtAnalysisInfo: Map[Stmt, analysis.type] = Map(); // "output" info as the end result of the analysis
    var blockAnalysisInfo: Map[Block, analysis.type] = Map(); // final states of all analysed blocks
    
    /**
     * Not sure if these getters are really necessary at the moment
     */
    def getAllInfo: Map[Stmt, analysis.type] = {
        stmtAnalysisInfo;
    }

    def getOneInfo(stmt: Stmt): analysis.type = {
        stmtAnalysisInfo.getOrElse(stmt, analysis.createLowest);
    }

    /**
     * Standard "do everything" function, inc. clearing unused info.
     */
    def doAnalysis: State = {
        analyseFunction("main");
        if debug then println(getAllInfo);

        previousStmtAnalysisState = null;
        blockAnalysisInfo = null;

        analysis.applyChanges(startState, getAllInfo);
    }

    /**
     * Generic function-analysis function.
     * Forms mutual recusion with analyseBlock and analyseStmt, where analyseStmt calls this on new CallStmts
     * 
     * N.B. Because of the way worklist algorithms work, any blocks that depend on a loop will be re-computed every time
     * until that loop is stable (i.e. further iterations make no changes). Ideally we could analyse the loop on it's own
     * and ignore the children until it stabilises.
     * 
     * For small programs this is negligible, but worst-case we have a large branching structure with many blocks that all
     * depend on an initial loop; this forces us to re-analyse every block until that original loop stabilises.
     */
    def analyseFunction(name: String): Unit = {
        if debug then println("analysing function: " + name);

        currentCallString = currentCallString + name;
        currentWorklist = findFunctionRootBlock(name);

        var functionStartAnalysisState: analysis.type = previousStmtAnalysisState;
        var currentFunctionAnalysedInfo: Map[Stmt, analysis.type] = Map();

        while (!currentWorklist.isEmpty) {
            var nextBlockToAnalyse: Block = currentWorklist.removeHead();

            // if the block has parents, take the combine of all parent blocks' final states
            // worklist should ensure that children get analysed at least once after all parents are resolved
            if (!getBlockParents(nextBlockToAnalyse).isEmpty) {
                getBlockParents(nextBlockToAnalyse).foreach(block => {
                    previousStmtAnalysisState = previousStmtAnalysisState.combine(blockAnalysisInfo.getOrElse(block, analysis.createLowest))
                });
            } else {
                // TODO: Should this be removed (keep previousStmtAnalysisState as functionStartAnalysisState?)
                previousStmtAnalysisState = analysis.createLowest;
            }

            currentFunctionAnalysedInfo = analyseBlock(nextBlockToAnalyse, currentFunctionAnalysedInfo);

            if (!currentWorklist.isEmpty) {
                // TODO: Should this be removed (keep previousStmtAnalysisState on loop?)
                // currently, for children of root block, previousStmtAnalysisState will be functionStartAnalysisState.combine(*root block's final state*)

                // N.B this code does solve a problem where final function states are carried into the start of the function, resulting in T for all statements.
                previousStmtAnalysisState = functionStartAnalysisState;
            }
        }

        // Once the entire function is done, save it.
        saveNewAnalysisInfo(currentFunctionAnalysedInfo);
        currentCallString = currentCallString.filter(funcName => {funcName != name});
    }

    /**
     * Analyses a block (of statements) by analysing each statement in .lines. We assume they are in execution order but this might not be guaranteed.
     * 
     * Updates the blockAnalysisInfo map at the end of all lines, and adds the block and all children to queue if it's changed, if they weren't already there.
     */
    def analyseBlock(block: Block, currentInfo: Map[Stmt, analysis.type]): Map[Stmt, analysis.type] = {
        if debug then println("analysing block: " + block.label);
        var outputInfo: Map[Stmt, analysis.type] = currentInfo;

        block.lines.foreach(blockStmt => {
            outputInfo = analyseStmt(blockStmt, outputInfo);
        })
        
        if (!previousStmtAnalysisState.asInstanceOf[analysis.type].equals(blockAnalysisInfo.getOrElse(block, null).asInstanceOf[analysis.type])) {
            blockAnalysisInfo = blockAnalysisInfo + (block -> previousStmtAnalysisState);

            // + block makes this remarkably convenient
            (getBlockChildren(block) + block).foreach(b => {
                if (!currentWorklist.contains(b)) {
                    currentWorklist.append(b);
                }
            })
        } else {
            // if nothing has changed, do nothing - the analysis will now be in a "wrap-up" stage where it's effectively just checking itself.
            ;
        }

        outputInfo;
    }

    /**
     * Analyses a single statement, from the known previous state.
     * 
     * Saves the new previousStmtAnalysisState and updates the per-function map of analysed info.
     * 
     * Also handles recursion and function calls by the match statement, which has a special case for CallStmts.
     */
    def analyseStmt(stmt: Stmt, currentInfo: Map[Stmt, analysis.type]): Map[Stmt, analysis.type] = {
        if debug then println("analysing stmt: " + stmt);
        var outputInfo: Map[Stmt, analysis.type] = currentInfo;
        
        stmt match {
            case functionCallStmt: CallStmt => {
                // if we have a function call, pause the current analysis and analyse the given function
                // effectively just inlines every function every time it's called, no function signatures.
                var inProgressWorklist: ArrayDeque[Block] = currentWorklist;

                if (!currentCallString.contains(functionCallStmt.funcName)) {
                    // pass through the CallStmt to the analysis so it knows what's happening, but only
                    // moves into the function if it's not a library function.
                    previousStmtAnalysisState = previousStmtAnalysisState.transfer(stmt);

                    outputInfo = currentInfo + (stmt -> previousStmtAnalysisState);

                    if (!analysis.libraryFunctions.contains(functionCallStmt.funcName)) {
                        analyseFunction(functionCallStmt.funcName);
                    }
                } else {
                    // ignores recursion for now.
                    // TODO: consider passing them as if they were library functions, let the analysis define how
                    // it handles recursion?
                    println(currentCallString);
                    println("ignoring recursive call in " + functionCallStmt.funcName);
                }

                currentWorklist = inProgressWorklist;
            }
            case _ => {
                previousStmtAnalysisState = previousStmtAnalysisState.transfer(stmt);

                outputInfo = currentInfo + (stmt -> previousStmtAnalysisState);
            }
        }

        outputInfo;
    }

    /**
     * The process for these two is similar:

     * Loop over all functions to find which one owns the given block (by label)
     * Gets the (string labels of) children or parents of that block from the owning function
     * Maps these string labels to blocks by
     *     Looping over all functions to find which owns the given block
     *     Getting the Block object from the owning function based on the label
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
     * The typesystem in this one has been painful to deal with.
     */
    def saveNewAnalysisInfo(newInfo: Map[Stmt, analysis.type]) = {
        var outputInfo: Map[Stmt, AnalysisPoint] = Map();

        newInfo.foreach((key: Stmt, value: analysis.type) => {
            outputInfo = outputInfo ++ Map(key -> 
                stmtAnalysisInfo.getOrElse(key, analysis.createLowest).asInstanceOf[analysis.type].combine(value)
            );
        })

        stmtAnalysisInfo = outputInfo.asInstanceOf[Map[Stmt, analysis.type]];
    }
}