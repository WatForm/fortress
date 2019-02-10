package fortress.formats;

import org.antlr.v4.runtime.tree.TerminalNode;

import fortress.tfol.*;
import java.util.List;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;
import java.util.stream.Collectors;


 // Visits a parse tree and constructs a theory
 // Only visits untyped FOL formulas; generates a typed theory
 // with a single type _UNIV
public class TptpToFortress extends FOFTPTPBaseVisitor {

    private Theory theory;

    private Type universeType = Type.mkTypeConst("_UNIV");
    private List<Term> formulas;
    private Set<FuncDecl> functionDeclarations;
    private Set<Var> primePropositions;

    public TptpToFortress(){
        this.theory = new Theory();
        this.formulas = new ArrayList<>();
        this.functionDeclarations = new HashSet<>();
        this.primePropositions = new HashSet<>();
    }
    
    public Theory getTheory() {
        return theory;
    }
    
    public Type getUniverseType() {
        return universeType;
    }
    
    @Override
    public Object visitSpec(FOFTPTPParser.SpecContext ctx) {
        for(FOFTPTPParser.Fof_annotatedContext f : ctx.fof_annotated()) {
            visit(f);
        }
        
        // Construct theory
        
        theory.addType(universeType);
        
        // Add function declarations
        for(FuncDecl f : functionDeclarations) {
            theory.addFunctionDeclaration(f);
        }
        
        // Add prime propositions as Bool constants
        for(Var p : primePropositions) {
            theory.addConstant(p.of(Type.Bool));
        }
        
        // Add free variables that are not prime propositions as constants of
        // the universe
        formulas.stream()
            .flatMap(formula -> Term.freeVariables(formula).stream())
            .filter(freeVar -> !primePropositions.contains(freeVar))
            .forEach(freeVar -> theory.addConstant(freeVar.of(universeType)));

        // Add axioms
        for(Term formula : formulas) {
            theory.addAxiom(formula);
        }
        
        return null;
    }

    // Add formulas as axioms, or if the formula is a conjecture, add its negation
    @Override
    public Object visitFof_annotated(FOFTPTPParser.Fof_annotatedContext ctx) {
        Term f = (Term) visit(ctx.fof_formula());
        if (ctx.ID(1).getText().equals("conjecture")) {
            formulas.add(Term.mkNot(f));
        }
        else {
            formulas.add(f);
        }
        return null;
    }

    @Override
    public Object visitNot(FOFTPTPParser.NotContext ctx) {
        Term formula = (Term) visit(ctx.fof_formula());
        return Term.mkNot(formula);
    }

    @Override
    public Object visitForall(FOFTPTPParser.ForallContext ctx) {
        List<AnnotatedVar> variables = new ArrayList<>();
        for(TerminalNode variableNode: ctx.ID()) {
            String name = variableNode.getText();
            variables.add(Term.mkVar(name).of(universeType));
        }
        Term body = (Term) visit(ctx.fof_formula());
        return Term.mkForall(variables, body);
    }

    @Override
    public Object visitExists(FOFTPTPParser.ExistsContext ctx) {
        List<AnnotatedVar> variables = new ArrayList<>();
        for (TerminalNode variableNode: ctx.ID()) {
            String name = variableNode.getText();
            variables.add(Term.mkVar(name).of(universeType));
        }
        Term body = (Term) visit(ctx.fof_formula());
        return Term.mkExists(variables, body);
    }

    @Override
    public Object visitAnd(FOFTPTPParser.AndContext ctx) {
        Term left = (Term) visit(ctx.fof_formula(0));
        Term right = (Term) visit(ctx.fof_formula(1));
        return Term.mkAnd(left, right);
    }

    @Override
    public Object visitOr(FOFTPTPParser.OrContext ctx) {
        Term left = (Term) visit(ctx.fof_formula(0));
        Term right = (Term) visit(ctx.fof_formula(1));
        return Term.mkOr(left, right);
    }

    @Override
    public Object visitImp(FOFTPTPParser.ImpContext ctx) {
        Term left = (Term) visit(ctx.fof_formula(0));
        Term right = (Term) visit(ctx.fof_formula(1));
        return Term.mkImp(left, right);
    }

    @Override
    public Object visitIff(FOFTPTPParser.IffContext ctx) {
        Term left = (Term) visit(ctx.fof_formula(0));
        Term right = (Term) visit(ctx.fof_formula(1));
        return Term.mkIff(left, right);
    }

    @Override
    public Object visitEq(FOFTPTPParser.EqContext ctx) {
        Term left = (Term) visit(ctx.term(0));
        Term right = (Term) visit(ctx.term(1));
        return Term.mkEq(left, right);
    }

    @Override
    public Object visitNeq(FOFTPTPParser.NeqContext ctx) {
        Term left = (Term) visit(ctx.term(0));
        Term right = (Term) visit(ctx.term(1));
        return Term.mkNot(Term.mkEq(left, right));
    }

    @Override
    public Object visitProp(FOFTPTPParser.PropContext ctx) {
        String name = ctx.ID().getText();
        Var v = Term.mkVar(name);
        primePropositions.add(v);
        return v;
    }

    @Override
    public Object visitPred(FOFTPTPParser.PredContext ctx) {
        String name = ctx.ID().getText();
        int numArgs = ctx.term().size();

        List<Type> argTypes = new ArrayList<>();
        List<Term> arguments = new ArrayList<>();
        for(int i = 0; i < numArgs; i++) {
            Term ti = (Term) visit(ctx.term(i));
            arguments.add(ti);
            argTypes.add(universeType);
        }
        
        // Remember what function signature we encountered
        FuncDecl p = FuncDecl.mkFuncDecl(name, argTypes, Type.Bool);
        functionDeclarations.add(p);
        
        return Term.mkApp(name, arguments);
    }

    @Override
    public Object visitParen(FOFTPTPParser.ParenContext ctx) {
        return visit(ctx.fof_formula());
    }

    @Override
    public Object visitConVar(FOFTPTPParser.ConVarContext ctx) {
        String name = ctx.ID().getText();
        return Term.mkVar(name);
    }

    @Override
    public Object visitApply(FOFTPTPParser.ApplyContext ctx) {
        String name = ctx.ID().getText();
        int numArgs = ctx.term().size();
        
        List<Type> argTypes = new ArrayList<>();
        List<Term> arguments = new ArrayList<>();
        for(int i = 0; i < numArgs; i++) {
            Term ti = (Term) visit(ctx.term(i));
            arguments.add(ti);
            argTypes.add(universeType);
        }
        
        // Remember what function signature we encountered
        FuncDecl f = FuncDecl.mkFuncDecl(name, argTypes, universeType);
        functionDeclarations.add(f);
        
        return Term.mkApp(name, arguments);
    }
}
