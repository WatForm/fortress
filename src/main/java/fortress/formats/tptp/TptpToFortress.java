package fortress.formats.tptp;

import org.antlr.v4.runtime.tree.TerminalNode;

import fortress.tfol.*;
import java.util.List;
import java.util.ArrayList;


 // Visits a parse tree and constructs a theory
 // Only visits untyped FOL formulas; generates a typed theory
 // with a single type _UNIV
public class TptpToFortress extends FOFTPTPBaseVisitor {

    private Theory theory;

    private Type universeType = Type.mkTypeConst("_UNIV");

    public TptpToFortress(){
        theory = new Theory();
    }
    
    public Theory getTheory() {
        // TODO need to add free vars to theory
        return theory;
    }
    
    public Type getUniverseType() {
        return universeType;
    }

    // Add formulas as axioms to the theory, or if the formula is a conjecture,
    // add its negation as an axiom
    @Override
    public Object visitFof_annotated(FOFTPTPParser.Fof_annotatedContext ctx) {
        Term f = (Term) visit(ctx.fof_formula());
        if (ctx.ID(1).getText().equals("conjecture")) {
            theory.addAxiom(Term.mkNot(f));
        }
        else {
            theory.addAxiom(f);
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
        // TODO need to remember this is a bool
        String name = ctx.ID().getText();
        return Term.mkVar(name);
    }

    @Override
    public Object visitPred(FOFTPTPParser.PredContext ctx) {
        // TODO need to remember types
        String name = ctx.ID().getText();
        int numArgs = ctx.term().size();

        List<Term> arguments = new ArrayList();
        for(int i = 0; i < numArgs; i++) {
            Term ti = (Term) visit(ctx.term(i));
            arguments.add(ti);
        }
        
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
        // TODO need to remember types
        String name = ctx.ID().getText();
        int numArgs = ctx.term().size();
        
        List<Term> arguments = new ArrayList<>();
        for(int i = 0; i < numArgs; i++) {
            Term ti = (Term) visit(ctx.term(i));
            arguments.add(ti);
        }
        
        return Term.mkApp(name, arguments);
    }
}
