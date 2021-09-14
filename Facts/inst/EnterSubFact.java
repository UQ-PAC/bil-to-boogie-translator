package Facts.inst;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

public class EnterSubFact extends InstFact {

    public String funcName;
    public List<String> inParams = new ArrayList<>();
    String outParam;
    public List<ParamFact> paramFacts = new ArrayList<>();

    public EnterSubFact(String pc, String funcName) {
        super(pc);
        this.funcName = funcName;
    }

    public String toString() {
        // todo: add param types
        StringBuilder line = new StringBuilder();
        line.append("procedure ").append(funcName).append("(");
        if (!inParams.isEmpty()) {
            line.append(inParams.get(0));
            for (int i = 1; i < inParams.size(); i++) {
                line.append(", ").append(inParams.get(i));
            }
        }
        line.append(")");
        if (outParam != null) {
            line.append(" returns (").append(outParam).append(")");
        }
        line.append(" {\n");
        return String.format("%s%s", label, line);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        EnterSubFact that = (EnterSubFact) o;
        return Objects.equals(funcName, that.funcName) && Objects.equals(inParams, that.inParams) && Objects.equals(outParam, that.outParam) && Objects.equals(paramFacts, that.paramFacts);
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), funcName, inParams, outParam, paramFacts);
    }
}