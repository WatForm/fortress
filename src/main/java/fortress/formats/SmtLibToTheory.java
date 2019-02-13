package fortress.formats;

import fortress.tfol.*;
import java.util.List;
import java.util.ArrayList;
import java.util.stream.Collectors;
import fortress.util.Errors;
import org.antlr.v4.runtime.misc.Interval;

public class SmtLibToTheory extends SmtLibSubsetBaseVisitor {
    
    private Theory theory;
    
    public int numAxioms = 0;
    
    public SmtLibToTheory() {
        this.theory = new Theory();
    }
    
    public Theory getTheory() {
        return theory;
    }
    
	@Override
    public Object visitDeclareconst(SmtLibSubsetParser.DeclareconstContext ctx) {
        Var x = Term.mkVar(ctx.ID(0).getText());
        Type type = Type.mkTypeConst(ctx.ID(1).getText());
        theory.addConstant(x.of(type));
        return null;
    }
    
    @Override
    public Object visitChecksat(SmtLibSubsetParser.ChecksatContext ctx) {
        // Do nothing, we ignore this for now
        return null;
    }
    
    @Override
    public Object visitExit(SmtLibSubsetParser.ExitContext ctx) {
        // Do nothing, we ignore this for now
        return null;
    }
	
	@Override
    public Object visitDeclarefun(SmtLibSubsetParser.DeclarefunContext ctx) {
        int lastIndex = ctx.ID().size() - 1;
        String function = ctx.ID(0).getText();
        Type returnType = Type.mkTypeConst(ctx.ID(lastIndex).getText());
        List<Type> argTypes = new ArrayList();
        for(int i = 1; i < lastIndex; i++) {
            argTypes.add(Type.mkTypeConst(ctx.ID(i).getText()));
        }
        FuncDecl decl = FuncDecl.mkFuncDecl(function, argTypes, returnType);
        theory.addFunctionDeclaration(decl);
        return null;
    }
    
    @Override
    public Object visitDeclaresort(SmtLibSubsetParser.DeclaresortContext ctx) {
        Type t = Type.mkTypeConst(ctx.ID().getText());
        theory.addType(t);
        return null;
    }

	@Override
    public Object visitAssertion(SmtLibSubsetParser.AssertionContext ctx) {
        numAxioms++;
        Term term = (Term) visit(ctx.term());
        // TODO Factor this somewhere -- useful code for future
        // int a = ctx.start.getStartIndex();
        // int b = ctx.stop.getStopIndex();
        // Interval interval = new Interval(a,b);
        // Errors.failIf(term == null, ctx.start.getInputStream().getText(interval));
        // Errors.failIf(theory == null);
        theory.addAxiom(term);
        return null;
    }

	@Override
    public Object visitTrue(SmtLibSubsetParser.TrueContext ctx) {
        return Term.mkTop();
    }

	@Override 
    public Object visitFalse(SmtLibSubsetParser.FalseContext ctx) { 
        return Term.mkBottom();
    }

	@Override
    public Object visitAnd(SmtLibSubsetParser.AndContext ctx) {
        List<Term> terms = ctx.term().stream().map(
            t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return Term.mkAnd(terms);
    }

	@Override
    public Object visitOr(SmtLibSubsetParser.OrContext ctx) {
        List<Term> terms = ctx.term().stream().map(
            t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return Term.mkOr(terms);
    }

	@Override
    public Object visitDistinct(SmtLibSubsetParser.DistinctContext ctx) {
        List<Term> terms = ctx.term().stream().map(
            t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return Term.mkDistinct(terms);
    }

	@Override
    public Object visitEq(SmtLibSubsetParser.EqContext ctx) {
        return Term.mkEq(
            (Term) visit(ctx.term(0)),
            (Term) visit(ctx.term(1))
        );
    }

	@Override
    public Object visitImp(SmtLibSubsetParser.ImpContext ctx) {
        return Term.mkImp(
            (Term) visit(ctx.term(0)),
            (Term) visit(ctx.term(1))
        );
    }

	@Override
    public Object visitNot(SmtLibSubsetParser.NotContext ctx) {
        return Term.mkNot( (Term) visit(ctx.term()) );
    }

	@Override
    public Object visitForall(SmtLibSubsetParser.ForallContext ctx) {
        List<AnnotatedVar> vars = ctx.binding().stream().map(
            binding -> (AnnotatedVar) visit(binding)
        ).collect(Collectors.toList());
        Term term = (Term) visit(ctx.term());
        return Term.mkForall(vars, term);
    }

	@Override
    public Object visitExists(SmtLibSubsetParser.ExistsContext ctx) {
        List<AnnotatedVar> vars = ctx.binding().stream().map(
            binding -> (AnnotatedVar) visit(binding)
        ).collect(Collectors.toList());
        Term term = (Term) visit(ctx.term());
        return Term.mkExists(vars, term);
    }

	@Override
    public Object visitVar(SmtLibSubsetParser.VarContext ctx) {
        return Term.mkVar(ctx.ID().getText());
    }

	@Override
    public Object visitBinding(SmtLibSubsetParser.BindingContext ctx) {
        Var x = Term.mkVar(ctx.ID(0).getText());
        Type t = Type.mkTypeConst(ctx.ID(1).getText());
        return x.of(t);
    }
    
    @Override
    public Object visitApplication(SmtLibSubsetParser.ApplicationContext ctx) {
        String function = ctx.ID().getText();
        List<Term> arguments = ctx.term().stream().map(
            t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return Term.mkApp(function, arguments);
    }
}
