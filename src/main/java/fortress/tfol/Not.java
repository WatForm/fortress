package fortress.tfol;

class Not extends Term {
    private Term body;
    
    protected Not(Term body){
        this.body = body;
    }
}
