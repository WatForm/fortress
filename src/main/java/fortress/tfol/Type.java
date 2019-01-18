package fortress.tfol;

public abstract class Type {
    public Type mkTypeConst(String name) {
        return new TypeConst(name);
    }
}
