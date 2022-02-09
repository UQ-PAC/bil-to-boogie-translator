package analysis;

import analysis.AnalysisPoint;
import astnodes.stmt.*;
import vcgen.State;

/**
 * Dummy "testing analysis" - keeps track of all the statements that it's seen so far, as a list.
 * Prints a line if it sees a call statement.
 */
class TestingAnalysis(state: Set[Stmt]) extends AnalysisPoint {
    private var currentState: Set[Stmt] = state;

    def this() = {
        this(Set());
    }

    override def applyChanges(preState: State, information: Map[Stmt, this.type]): State = {
        preState;
    }

    override def equals(other: this.type): Boolean = {
        if other == null then return false;

        this.toString == other.toString
    }

    override def compare(other: this.type): Int = {
        (this.currentState.size - other.currentState.size).sign;
    }

    override def join(other: this.type): this.type = {
        TestingAnalysis(currentState.union(other.currentState)).asInstanceOf[this.type];
    }

    override def meet(other: this.type): this.type = {
        TestingAnalysis(currentState.intersect(other.currentState)).asInstanceOf[this.type];
    }

    override def transfer(stmt: Stmt): this.type = {
        var newState: Set[Stmt] = Set();
        stmt match {
            case callStmt: CallStmt => {
                if (!currentState.contains(stmt)) {
                    newState = currentState ++ Set(stmt);
                } else {
                    newState = currentState;
                }
            }
            case _ => {
                if (!currentState.contains(stmt)) {
                    newState = currentState ++ Set(stmt);
                } else {
                    newState = currentState;
                }
            };
        }

        TestingAnalysis(newState).asInstanceOf[this.type];
    }

    override def createLowest: this.type = {
        TestingAnalysis(Set()).asInstanceOf[this.type];
    }

    override def toString: String = {
        "TestingAnalysis: " + this.currentState;
    }
}