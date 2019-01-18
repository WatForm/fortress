package fortress.tfol;

class Var extends Term {
    private String name;
    private Type type;
    
    protected Var(String name, Type type) {
        this.name = name;
        this.type = type;
    }
}
