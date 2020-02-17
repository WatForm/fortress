package fortress.inputs;

import fortress.msfol.*;
import java.util.List;
import java.util.ArrayList;
import java.util.stream.Collectors;
import fortress.util.Errors;
import org.antlr.v4.runtime.misc.Interval;
import java.util.Optional;
import java.util.Map;
import java.util.HashMap;
import java.lang.Void;

public class SmtLibVisitor extends SmtLibSubsetBaseVisitor {

    private Theory theory;
    private Map<String, String> info;
    private Optional<String> logic;

    protected int numAxioms;

    public SmtLibVisitor() {
        this.theory = Theory.empty();
        this.info = new HashMap<>();
        this.logic = Optional.empty();
        this.numAxioms = 0;
    }

    public Theory getTheory() {
        return theory;
    }

    public Map<String, String> getInfo() {
        return info;
    }

    public Optional<String> getLogic() {
        return logic;
    }

    private static class AttributePair {
        public String attributeName;
        public String attributeValue;

        public AttributePair(String attributeName, String attributeValue) {
            this.attributeName = attributeName;
            this.attributeValue = attributeValue;
        }
    }

    private Sort parseSort(String name) {
        if (name.equals("Bool")) {
            return Sort.Bool();
        } else if (name.equals("Int")) {
            return Sort.Int();
        } else {
            return Sort.mkSortConst(name);
        }
    }

    @Override
    public Sort visitSort_name(SmtLibSubsetParser.Sort_nameContext ctx) {
        Sort s = parseSort(ctx.ID().getText());

        if (!theory.signature().hasSort(s)) {
            theory = theory.withSort(s);
        }

        return s;
    }

    @Override
    public Sort visitBv_sort(SmtLibSubsetParser.Bv_sortContext ctx) {
        int width = Integer.parseInt(ctx.NUMBER().getText());
        if (width <= 0) throw new ParserException("BitVector must have positive width");

        Sort s = Sort.BitVector(width);

        if (!theory.signature().hasSort(s)) {
            theory = theory.withSort(s);
        }

        return s;
    }

    @Override
    public Void visitDeclare_const(SmtLibSubsetParser.Declare_constContext ctx) {
        Var x = Term.mkVar(ctx.ID().getText());
        Sort sort = (Sort) visit(ctx.sort());
        theory = theory.withConstant(x.of(sort));
        return null;
    }

    @Override
    public Void visitDeclare_fun(SmtLibSubsetParser.Declare_funContext ctx) {
        int lastIndex = ctx.sort().size() - 1;
        String function = ctx.ID().getText();
        Sort returnSort = (Sort) visit(ctx.sort(lastIndex));
        List<Sort> argSorts = new ArrayList<>();
        for (int i = 0; i < lastIndex; i++) {
            argSorts.add((Sort) visit(ctx.sort(i)));
        }
        FuncDecl decl = FuncDecl.mkFuncDecl(function, argSorts, returnSort);
        theory = theory.withFunctionDeclaration(decl);
        return null;
    }

    @Override
    public Void visitDeclare_sort(SmtLibSubsetParser.Declare_sortContext ctx) {
        Sort t = Sort.mkSortConst(ctx.ID().getText());
        theory = theory.withSort(t);
        return null;
    }

    @Override
    public Void visitAssert(SmtLibSubsetParser.AssertContext ctx) {
        Term term = (Term) visit(ctx.term());
        // TODO Factor this somewhere -- useful code for future
        // int a = ctx.start.getStartIndex();
        // int b = ctx.stop.getStopIndex();
        // Interval interval = new Interval(a,b);
        // Errors.failIf(term == null, ctx.start.getInputStream().getText(interval));
        // Errors.failIf(theory == null);
        theory = theory.withAxiom(term);
        this.numAxioms++;
        return null;
    }

    @Override
    public Void visitCheck_sat(SmtLibSubsetParser.Check_satContext ctx) {
        // Do nothing, we ignore this for now
        return null;
    }

    @Override
    public Void visitSet_info(SmtLibSubsetParser.Set_infoContext ctx) {
        AttributePair attributePair = (AttributePair) visit(ctx.attribute());
        info.put(attributePair.attributeName, attributePair.attributeValue);
        return null;
    }

    @Override
    public Void visitSet_logic(SmtLibSubsetParser.Set_logicContext ctx) {
        logic = Optional.of(ctx.ID().getText());
        return null;
    }

    @Override
    public Void visitGet_model(SmtLibSubsetParser.Get_modelContext ctx) {
        // Do nothing, we ignore this for now
        return null;
    }

    @Override
    public Void visitExit(SmtLibSubsetParser.ExitContext ctx) {
        // Do nothing, we ignore this for now
        return null;
    }

    @Override
    public AttributePair visitAttribute_id(SmtLibSubsetParser.Attribute_idContext ctx) {
        String attributeName = ctx.ID(0).getText();
        String attributeValue = ctx.ID(1).getText();
        return new AttributePair(attributeName, attributeValue);
    }

    @Override
    public AttributePair visitAttribute_quote(SmtLibSubsetParser.Attribute_quoteContext ctx) {
        String attributeName = ctx.ID().getText();
        // Chop off the pipes 
        String wholeQuote = ctx.QUOTE().getText();
        String attributeValue = wholeQuote.substring(1, wholeQuote.length() - 1);
        return new AttributePair(attributeName, attributeValue);
    }

    @Override
    public AttributePair visitAttribute_string(SmtLibSubsetParser.Attribute_stringContext ctx) {
        String attributeName = ctx.ID().getText();
        // Chop off the quotes
        String wholeString = ctx.STRING().getText();
        String attributeValue = wholeString.substring(1, wholeString.length() - 1);
        return new AttributePair(attributeName, attributeValue);
    }

    @Override
    public Term visitTrue(SmtLibSubsetParser.TrueContext ctx) {
        return Term.mkTop();
    }

    @Override
    public Term visitFalse(SmtLibSubsetParser.FalseContext ctx) {
        return Term.mkBottom();
    }

    @Override
    public Term visitAnd(SmtLibSubsetParser.AndContext ctx) {
        List<Term> terms = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return Term.mkAnd(terms);
    }

    @Override
    public Term visitOr(SmtLibSubsetParser.OrContext ctx) {
        List<Term> terms = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return Term.mkOr(terms);
    }

    @Override
    public Term visitDistinct(SmtLibSubsetParser.DistinctContext ctx) {
        List<Term> terms = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return Term.mkDistinct(terms);
    }

    @Override
    public Term visitEq(SmtLibSubsetParser.EqContext ctx) {
        if (ctx.term().size() == 2) {
            return Term.mkEq(
                    (Term) visit(ctx.term(0)),
                    (Term) visit(ctx.term(1))
            );
        }

        // (= a b c) is short for (and (= a b) (= b c))
        List<Term> equalities = new ArrayList<>();
        for (int i = 0; i < ctx.term().size() - 1; i++) {
            equalities.add(Term.mkEq(
                    (Term) visit(ctx.term(i)),
                    (Term) visit(ctx.term(i + 1))
            ));
        }
        return Term.mkAnd(equalities);
    }

    @Override
    public Term visitImp(SmtLibSubsetParser.ImpContext ctx) {
        if (ctx.term().size() == 2) {
            return Term.mkImp(
                    (Term) visit(ctx.term(0)),
                    (Term) visit(ctx.term(1))
            );
        }

        // (=> x y z) is short for (=> x (=> y z)
        List<Term> terms = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return generateImp(terms);
    }

    private Term generateImp(List<Term> terms) {
        if (terms.size() == 2) {
            return Term.mkImp(terms.get(0), terms.get(1));
        } else {
            // TODO Could be made more efficient
            return Term.mkImp(
                    terms.get(0),
                    generateImp(terms.subList(1, terms.size() - 1))
            );
        }
    }

    @Override
    public Term visitNot(SmtLibSubsetParser.NotContext ctx) {
        return Term.mkNot((Term) visit(ctx.term()));
    }

    @Override
    public Term visitForall(SmtLibSubsetParser.ForallContext ctx) {
        List<AnnotatedVar> vars = ctx.binding().stream().map(
                binding -> (AnnotatedVar) visit(binding)
        ).collect(Collectors.toList());
        Term term = (Term) visit(ctx.term());
        return Term.mkForall(vars, term);
    }

    @Override
    public Term visitExists(SmtLibSubsetParser.ExistsContext ctx) {
        List<AnnotatedVar> vars = ctx.binding().stream().map(
                binding -> (AnnotatedVar) visit(binding)
        ).collect(Collectors.toList());
        Term term = (Term) visit(ctx.term());
        return Term.mkExists(vars, term);
    }

    @Override
    public Term visitVar(SmtLibSubsetParser.VarContext ctx) {
        return Term.mkVar(ctx.ID().getText());
    }

    @Override
    public AnnotatedVar visitBinding(SmtLibSubsetParser.BindingContext ctx) {
        Var x = Term.mkVar(ctx.ID().getText());
        Sort t = (Sort) visit(ctx.sort());
        return x.of(t);
    }

    @Override
    public Term visitApplication(SmtLibSubsetParser.ApplicationContext ctx) {
        String function = ctx.ID().getText();
        List<Term> arguments = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return Term.mkApp(function, arguments);
    }

    @Override
    public Term visitTerm_with_attributes(SmtLibSubsetParser.Term_with_attributesContext ctx) {
        // Ignore the attributes for now
        return (Term) visit(ctx.term());
    }


    @Override
    public Term visitInt_literal(SmtLibSubsetParser.Int_literalContext ctx) {
        int constant = Integer.parseInt(ctx.NUMBER().getText());
        return new IntegerLiteral(constant);
    }

    @Override
    public Term visitNeg(SmtLibSubsetParser.NegContext ctx) {
        Term argument = (Term) visit(ctx.term());
        return Term.mkNeg(argument);
    }

    @Override
    public Term visitSub(SmtLibSubsetParser.SubContext ctx) {
        List<Term> arguments = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        Optional<Term> opList = arguments.stream().reduce(Term::mkSub);
        return opList.orElse(null);
    }

    @Override
    public Term visitPlus(SmtLibSubsetParser.PlusContext ctx) {
        List<Term> arguments = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        Optional<Term> opList = arguments.stream().reduce(Term::mkPlus);
        return opList.orElse(null);
    }
    @Override
    public Term visitMult(SmtLibSubsetParser.MultContext ctx) {
        List<Term> arguments = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        Optional<Term> opList = arguments.stream().reduce(Term::mkMult);
        return opList.orElse(null);
    }
    @Override
    public Term visitDiv(SmtLibSubsetParser.DivContext ctx) {
        List<Term> arguments = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        Optional<Term> opList = arguments.stream().reduce(Term::mkDiv);
        return opList.orElse(null);
    }
    @Override
    public Term visitMod(SmtLibSubsetParser.ModContext ctx) {
        List<Term> arguments = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return Term.mkMod(arguments.get(0), arguments.get(1));
    }
    @Override
    public Term visitAbs(SmtLibSubsetParser.AbsContext ctx) {
        throw new ParserException("Absolute value for int is not supported");
    }
    @Override
    public Term visitLe(SmtLibSubsetParser.LeContext ctx) {
        List<Term> arguments = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        List<Term> comps = new ArrayList<Term>();
        for (int i = 1; i < arguments.size(); i++) {
            comps.add(Term.mkLE(arguments.get(i - 1), arguments.get(i)));
        }
        return Term.mkAnd(comps);
    }
    @Override
    public Term visitLt(SmtLibSubsetParser.LtContext ctx) {
        List<Term> arguments = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        List<Term> comps = new ArrayList<Term>();
        for (int i = 1; i < arguments.size(); i++) {
            comps.add(Term.mkLT(arguments.get(i - 1), arguments.get(i)));
        }
        return Term.mkAnd(comps);
    }
    @Override
    public Term visitGe(SmtLibSubsetParser.GeContext ctx) {
        List<Term> arguments = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        List<Term> comps = new ArrayList<Term>();
        for (int i = 1; i < arguments.size(); i++) {
            comps.add(Term.mkGE(arguments.get(i - 1), arguments.get(i)));
        }
        return Term.mkAnd(comps);
    }
    @Override
    public Term visitGt(SmtLibSubsetParser.GtContext ctx) {
        List<Term> arguments = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());
        List<Term> comps = new ArrayList<Term>();
        for (int i = 1; i < arguments.size(); i++) {
            comps.add(Term.mkGT(arguments.get(i - 1), arguments.get(i)));
        }
        return Term.mkAnd(comps);
    }

    @Override
    public Term visitBin_literal(SmtLibSubsetParser.Bin_literalContext ctx) {
        String bin = ctx.BIN_NUMBER().getText();

        int width = bin.length() - 2;
        int val = Integer.parseInt(bin.substring(2), 2);

        return new BitVectorLiteral(val, width);
    }
    @Override
    public Term visitHex_literal(SmtLibSubsetParser.Hex_literalContext ctx) {
        String bin = ctx.HEX_NUMBER().getText();

        int width = (bin.length() - 2) * 4;
        int val = Integer.parseInt(bin.substring(2), 16);

        return new BitVectorLiteral(val, width);
    }
    @Override
    public Term visitBvconcat(SmtLibSubsetParser.BvconcatContext ctx) {
        throw new ParserException("Concatenation for BitVectors is not supported");
    }
    @Override
    public Term visitBvnot(SmtLibSubsetParser.BvnotContext ctx) {
        throw new ParserException("Not for BitVectors is not supported is not supported");
    }
    @Override
    public Term visitBvneg(SmtLibSubsetParser.BvnegContext ctx) {
        Term arg = (Term) visit(ctx.term());
        return Term.mkBvNeg(arg);
    }
    @Override
    public Term visitBvand(SmtLibSubsetParser.BvandContext ctx) {
        throw new ParserException("And for BitVectors is not supported is not supported");
    }
    @Override
    public Term visitBvor(SmtLibSubsetParser.BvorContext ctx) {
        throw new ParserException("Or for BitVectors is not supported is not supported");
    }
    @Override
    public Term visitBvadd(SmtLibSubsetParser.BvaddContext ctx) {
        Term arg0 = (Term) visit(ctx.term(0));
        Term arg1 = (Term) visit(ctx.term(1));
        return Term.mkBvPlus(arg0, arg1);
    }
    @Override
    public Term visitBvmul(SmtLibSubsetParser.BvmulContext ctx) {
        Term arg0 = (Term) visit(ctx.term(0));
        Term arg1 = (Term) visit(ctx.term(1));
        return Term.mkBvMult(arg0, arg1);
    }
    @Override
    public Term visitBvudiv(SmtLibSubsetParser.BvudivContext ctx) {
        throw new ParserException("Unsigned division for BitVectors is not supported is not supported");
    }
    @Override
    public Term visitBvurem(SmtLibSubsetParser.BvuremContext ctx) {
        throw new ParserException("Unsigned remainder for BitVectors is not supported is not supported");
    }
    @Override
    public Term visitBvshl(SmtLibSubsetParser.BvshlContext ctx) {
        throw new ParserException("Shift left for BitVectors is not supported is not supported");
    }
    @Override
    public Term visitBvshr(SmtLibSubsetParser.BvshrContext ctx) {
        throw new ParserException("Shift right for BitVectors is not supported is not supported");
    }
}
