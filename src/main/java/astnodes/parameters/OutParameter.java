package astnodes.parameters;
import astnodes.exp.var.Register;

public class OutParameter extends Parameter {

    public OutParameter(Register name, Register register) {
        super(name, register);
    }
    
    // TODO hack

    @Override
    public String toString() {
        return String.format("%s: bv%d, Gamma_%s: bool", getName(), getName().size().get(), getName());
    }
}
