package fortress.inputs;

import java.io.*; 

import fortress.msfol.*;
import fortress.operations.TermOps;

import java.util.List;
import java.util.ArrayList;
import java.util.stream.Collectors;
// import fortress.util.Errors;
import fortress.util.NameConverter;

import org.antlr.v4.runtime.misc.Interval;

import java.util.Optional;
import java.util.Map;
import java.util.HashMap;
import java.lang.Void;

import static scala.jdk.javaapi.OptionConverters.toJava;




public class SmtLibVisitor extends SmtLibSubsetBaseVisitor {

    private Theory theory;
    private Map<String, String> info;
    private Optional<String> logic;

    // Used to determine if we treat functions named `closure` as transitive closure and 'cardinality' as set cardinality or not
    private boolean usingSmtPlus = false;

    protected int numAxioms;

    public SmtLibVisitor(boolean usingSmtPlus) {
        this.theory = Theory.empty();
        this.info = new HashMap<>();
        this.logic = Optional.empty();
        this.numAxioms = 0;
        this.usingSmtPlus = usingSmtPlus;
    }
    public SmtLibVisitor(){
        this(false);
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

    public boolean usingSmtPlus(){
        return this.usingSmtPlus;
    }

    public void setUsingSmtPlus(boolean value){
        this.usingSmtPlus = value;
    }

    private static class AttributePair {
        public String attributeName;
        public String attributeValue;

        public AttributePair(String attributeName, String attributeValue) {
            this.attributeName = attributeName;
            this.attributeValue = attributeValue;
        }
    }

    private static class VarTermPair {
        public Var v;
        public Term t;

        public VarTermPair(Var v, Term t) {
            this.v = v;
            this.t = t;
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
        Sort s = parseSort(NameConverter.nameWithoutQuote(ctx.ID().getText()));

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
        //Var x = Term.mkVar(ctx.ID().getText());
        // Term could be a domain element
        String varName = NameConverter.nameWithoutQuote(ctx.ID().getText());
        Optional<DomainElement> oDomainValue = toJava(DomainElement.interpretName(varName));
        if (oDomainValue.isPresent()){
            // no constant needs defining
            return null;
        }
        Var x = Term.mkVar(varName);
        Sort sort = (Sort) visit(ctx.sort());
        theory = theory.withConstantDeclaration(x.of(sort));
        return null;
    }

    @Override
    public Void visitDeclare_fun(SmtLibSubsetParser.Declare_funContext ctx) {
        int lastIndex = ctx.sort().size() - 1;
        if (lastIndex == 0) {
            // declare-fun used to declare-const
            Var x = Term.mkVar(NameConverter.nameWithoutQuote(ctx.ID().getText()));
            Sort sort = (Sort) visit(ctx.sort(lastIndex));
            theory = theory.withConstantDeclaration(x.of(sort));
        } else {
            String function = NameConverter.nameWithoutQuote(ctx.ID().getText());
            Sort returnSort = (Sort) visit(ctx.sort(lastIndex));
            List<Sort> argSorts = new ArrayList<>();
            for (int i = 0; i < lastIndex; i++) {
                argSorts.add((Sort) visit(ctx.sort(i)));
            }
            FuncDecl decl = FuncDecl.mkFuncDecl(function, argSorts, returnSort);
            theory = theory.withFunctionDeclaration(decl);
        }
        return null;
    }

    @Override
    public Void visitDefine_fun(SmtLibSubsetParser.Define_funContext ctx) { // '(' 'define-fun' ID '(' sorted_var* ')' sort term ')'
        // If functions are defined with 0 arguments, we treat them as a constant definition rather than a function
        String funcName = NameConverter.nameWithoutQuote(ctx.ID().getText());
        int argNum = ctx.sorted_var().size();
        List<AnnotatedVar> argList = new ArrayList<>();
        for(int i=0; i<argNum; i++) {
            argList.add( visitSorted_var( ctx.sorted_var(i) ) );
        }
        Sort resultSort = (Sort)visit(ctx.sort());
        Term funcBody = (Term)visit(ctx.term());

        // Definition or constant
        if (argNum == 0){
            ConstantDefinition cDef = ConstantDefinition.mkConstantDefinition(Term.mkVar(funcName).of(resultSort), funcBody);
            theory = this.theory.withConstantDefinition(cDef);
        } else {
            FunctionDefinition funcDef = FunctionDefinition.mkFunctionDefinition(funcName, argList, resultSort, funcBody);
            theory = this.theory.withFunctionDefinition(funcDef);
        }
        return null;
    }

    @Override
    public AnnotatedVar visitSorted_var(SmtLibSubsetParser.Sorted_varContext ctx) {
        String name = NameConverter.nameWithoutQuote(ctx.ID().getText());
        Var var = Term.mkVar(name);
        Sort sort = (Sort)visit(ctx.sort());
        return new AnnotatedVar(var, sort);
    }

    @Override
    public Void visitDeclare_sort(SmtLibSubsetParser.Declare_sortContext ctx) {
        Sort t = Sort.mkSortConst(NameConverter.nameWithoutQuote(ctx.ID().getText()));
        // Parser requires this number to be 0 now (no more NAT_NUMBER)
        // int n = Integer.parseInt(ctx.NAT_NUMBER().getText());
        // if (n != 0) throw new ParserException("Sort declared with non-zero parameters");
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
        logic = Optional.of(NameConverter.nameWithoutQuote(ctx.ID().getText()));
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
        String attributeName = NameConverter.nameWithoutQuote(ctx.ID(0).getText());
        String attributeValue = NameConverter.nameWithoutQuote(ctx.ID(1).getText());
        //System.out.println("--- '" + attributeValue+"'");
        //System.out.println("+++ '"+ ctx.ID(1).getText()+"'");
        return new AttributePair(attributeName, attributeValue);
    }

    /*
    @Override
    public AttributePair visitAttribute_quote(SmtLibSubsetParser.Attribute_quoteContext ctx) {
        String attributeName = ctx.ID().getText();
        // Chop off the pipes 
        String wholeQuote = ctx.QUOTE().getText();
        String attributeValue = wholeQuote.substring(1, wholeQuote.length() - 1);
        return new AttributePair(attributeName, attributeValue);
    }
    */

    @Override
    public AttributePair visitAttribute_string(SmtLibSubsetParser.Attribute_stringContext ctx) {
        String attributeName = NameConverter.nameWithoutQuote(ctx.ID().getText());
        // Chop off the quotes
        String wholeString = ctx.STRING().getText();
        String attributeValue = wholeString.substring(1, wholeString.length() - 1);
        return new AttributePair(attributeName, attributeValue);
    }

    @Override
    public AttributePair visitAttribute_dec_digit(SmtLibSubsetParser.Attribute_dec_digitContext ctx) {
        String attributeName = NameConverter.nameWithoutQuote(ctx.ID().getText());
        // treat number as a string
        String attributeValue = ctx.DEC_DIGIT().getText();
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
    public Term visitLet(SmtLibSubsetParser.LetContext ctx) {
        List<VarTermPair> vartermlist = ctx.letbinding().stream().map(
                letbinding -> (VarTermPair) visit(letbinding)
        ).collect(Collectors.toList());
        Term term = (Term) visit(ctx.term());
        Term t = term ;
        // now have list of (var,term) and have to substitute these into the term
        // let statements in SMT-LIB are parallel substitutions
        for (int i = 0; i < vartermlist.size(); i++) {
            Var v = vartermlist.get(i).v ;
            Term vt = vartermlist.get(i).t ;
            t = TermOps.wrapTerm(t).substitute(v,vt) ;
        } ;
        return t;
    }

    @Override
    public Term visitIte(SmtLibSubsetParser.IteContext ctx) {
        Term t1 = (Term) visit(ctx.term(0));
        Term t2 = (Term) visit(ctx.term(1));
        Term t3 = (Term) visit(ctx.term(2));
        return Term.mkIfThenElse(t1,t2,t3);
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
        String varName = NameConverter.nameWithoutQuote(ctx.ID().getText());
        return Term.mkDomainElementOrVar(varName);
    }

    @Override
    public VarTermPair visitLetbinding(SmtLibSubsetParser.LetbindingContext ctx) {
        String xName = NameConverter.nameWithoutQuote(ctx.ID().getText());
        Var x = Term.mkVar(xName);
        Term t = (Term) visit(ctx.term()) ;
        return new VarTermPair(x, t) ;
    }

    @Override
    public AnnotatedVar visitBinding(SmtLibSubsetParser.BindingContext ctx) {
        String xName = NameConverter.nameWithoutQuote(ctx.ID().getText());
        Var x = Term.mkVar(xName);
        Sort t = (Sort) visit(ctx.sort());
        return x.of(t);
    }

    @Override
    public Term visitApplication(SmtLibSubsetParser.ApplicationContext ctx) {
        String function = NameConverter.nameWithoutQuote(ctx.ID().getText());

        List<Term> arguments = ctx.term().stream().map(
                t -> (Term) visit(t)
        ).collect(Collectors.toList());

        // We treat "closure as a transitive closure if using smt+"
        if (usingSmtPlus && (function.equals("closure") || function.equals("reflexive-closure")) ){
            // Check that we have at least 2 args and the function name
            if (arguments.size() < 3){
                throw new ParserException("Error at " + ctx.start.toString() + " closure must have at least 3 arguments. Got " + arguments.size()+".");
            }
            String functionName;
            try{
                functionName = ((Var)arguments.get(0)).getName();
            } catch (ClassCastException e){
                throw new ParserException("Trying to make closure, but function name could not be found.");
            }
            // Don't include the name
            // the first two arguments are the start and end of the closure
            Term start = arguments.get(1);
            Term end = arguments.get(2);
            List<Term> fixedArguments = arguments.subList(3, arguments.size());

            if(function.equals("closure")){
                return Term.mkClosure(functionName, start, end, fixedArguments);
            } else{
                return Term.mkReflexiveClosure(functionName, start, end, fixedArguments);
            }
        } 

        // if we see 'cardinality', deal with it accordingly
        else if (usingSmtPlus && function.equals("cardinality")){
            // Check that we have only 1 arg
            if (arguments.size() != 1){
                throw new ParserException("Error at " + ctx.start.toString() + " cardinality must have at exacrly 1 argument. Got " + arguments.size()+".");
            }
            String functionName;
            try{
                functionName = ((Var)arguments.get(0)).getName();
            } catch (ClassCastException e){
                throw new ParserException("Trying to make cardinality, but function name could not be found.");
            }
            
            return Term.mkSetCardinality(functionName);
        } 
        // Otherwise just treat as a function application
        return Term.mkApp(function, arguments);
    }

    /*
    @Override
    public Term visitClosure(SmtLibSubsetParser.ClosureContext ctx) {
        String function = NameConverter.nameWithoutQuote(ctx.ID().getText());
        List<Term> arguments = ctx.term().stream().map(
            t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return Term.mkClosure(function, arguments.get(0), arguments.get(1), arguments.subList(2, arguments.size()));
    }
    

    @Override
    public Term visitReflexive_closure(SmtLibSubsetParser.Reflexive_closureContext ctx) {
        String function = NameConverter.nameWithoutQuote(ctx.ID().getText());
        List<Term> arguments = ctx.term().stream().map(
            t -> (Term) visit(t)
        ).collect(Collectors.toList());
        return Term.mkReflexiveClosure(function, arguments.get(0), arguments.get(1), arguments.subList(2, arguments.size()));
    }
    */

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
    public Term visitInt_zero(SmtLibSubsetParser.Int_zeroContext ctx) {
        int constant = Integer.parseInt(ctx.ZERO().getText());
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

    private int valueToSignedBitVector(int val, int bitwidth){
        val %= (int)Math.pow(2, bitwidth);
        // Val is now essentially unsigned bv of bitwidth
        if ((val & (1 << (bitwidth - 1))) != 0){
            // Sign bit is set make it negative
            val = val - (1 << bitwidth);
        }
        return val;
    }

    @Override
    public Term visitBin_literal(SmtLibSubsetParser.Bin_literalContext ctx) {
        String bin = ctx.BIN_NUMBER().getText();

        int width = bin.length() - 2;
        int val = Integer.parseInt(bin.substring(2), 2);

        val = valueToSignedBitVector(val, width);

        return new BitVectorLiteral(val, width);
    }
    @Override
    public Term visitHex_literal(SmtLibSubsetParser.Hex_literalContext ctx) {
        String bin = ctx.HEX_NUMBER().getText();

        int width = (bin.length() - 2) * 4; // hex has 4 bits per character
        int val = Integer.parseInt(bin.substring(2), 16);

        val = valueToSignedBitVector(val, width);

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
