package fortress.tfol;

class Implication extends Term {
    private Term antecedent;
    private Term consequent;
    
    protected Implication(Term antecedent, Term consequent) {
        this.antecedent = antecedent;
        this.consequent = consequent;
    }
}
