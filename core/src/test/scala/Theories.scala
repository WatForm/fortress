import fortress.msfol._

object Theories {
    
    // Transitive relation R
    // Anti symmetric
    // Anti reflexive
    // BiggerFish: For every x, there exists y such that x R y
    // Should be satisfiable only for infinite domains, or empty domains
    // public static Theory lessThanInfinite = makeLessThanInfinite()
    
    // Group theory axioms
    
    val G = Sort.mkSortConst("G") // group type
    val e = Var("e") // identity element
    val f = FuncDecl.mkFuncDecl("f", G, G, G) // group operation
    
    val groupTheory: Theory = {
        val x = Var("x")
        val y = Var("y")
        val z = Var("z")
        
        val associativeAxiom = Forall(Seq(x.of(G), y.of(G), z.of(G)),
            Eq(
                App("f", App("f", x, y), z),
                App("f", x, App("f", y, z))))
        
        val identityAxiom = Forall(x.of(G),
            And(
                Eq(App("f", x, e), x),
                Eq(App("f", e, x), x)))
        
        val inverseAxiom = Forall(x.of(G), Exists(y.of(G), 
            And(
                Eq(App("f", x, y), e),
                Eq(App("f", y, x), e))))
                
        Theory.empty
            .withSort(G)
            .withConstantDeclaration(e.of(G))
            .withFunctionDeclaration(f)
            .withAxiom(associativeAxiom)
            .withAxiom(identityAxiom)
            .withAxiom(inverseAxiom)
    }
    
    val nonAbelianGroupTheory: Theory = {
        val x = Var("x")
        val y = Var("y")
        val abelianAssertion = Forall(Seq(x.of(G), y.of(G)),
            Eq(
                App("f", x, y),
                App("f", y, x)))
        groupTheory.withAxiom(Not(abelianAssertion))
    }
}
