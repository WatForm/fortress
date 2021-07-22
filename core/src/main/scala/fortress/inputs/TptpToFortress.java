package fortress.inputs;

import fortress.util.Errors;
import org.antlr.v4.runtime.tree.TerminalNode;

import fortress.msfol.*;

import java.util.*;
import java.io.*;

import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

 // Visits a parse tree and constructs a theory
 // Only visits unsorted FOL formulas; generates a sorted theory
 // with a single sorted _UNIV
public class TptpToFortress extends FOFTPTPBaseVisitor {

    private Theory theory;

    private Sort universeSort = Sort.mkSortConst("_UNIV");
    private List<Term> formulas;
    private Set<FuncDecl> functionDeclarations;
    private Set<Var> primePropositions;
    private String filePath;
    private Optional<String> errorMessage = Optional.empty();

    public TptpToFortress(){
        this.theory = Theory.empty().withSort(universeSort);
        this.formulas = new ArrayList<>();
        this.functionDeclarations = new HashSet<>();
        this.primePropositions = new HashSet<>();
    }

    public TptpToFortress(String filePath) {
        this.theory = Theory.empty().withSort(universeSort);
        this.formulas = new ArrayList<>();
        this.functionDeclarations = new HashSet<>();
        this.primePropositions = new HashSet<>();
        this.filePath = filePath;
    }

    public Either<Errors.ParserError, Theory> getTheory() {
        if (errorMessage.isPresent()) return new Left<>(new Errors.ParserError(errorMessage.get()));
        else return new Right<>(theory);
    }
    
    public Sort getUniverseSort() {
        return universeSort;
    }
    
    @Override
    public Void visitSpec(FOFTPTPParser.SpecContext ctx) {
        for(FOFTPTPParser.LineContext f : ctx.line()) {
            visit(f);
        }
        
        // Construct theory
        // Add function declarations
        theory = theory.withFunctionDeclarations(functionDeclarations);
        
        // Add prime propositions as Bool constants
        for(Var p : primePropositions) {
            theory = theory.withConstant(p.of(Sort.Bool()));
        }
        
        // Add free variables that are not prime propositions as constants of
        // the universe
        formulas.stream()
            .flatMap(formula -> formula.freeVarConstSymbolsJava().stream())
            .filter(freeVar -> !primePropositions.contains(freeVar))
            .forEach(freeVar -> theory = theory.withConstant(freeVar.of(universeSort)));

        // Add axioms
        theory = theory.withAxioms(formulas);
        
        return null;
    }

    // Add formulas as axioms, or if the formula is a conjecture, add its negation
    @Override
    public Term visitFof_annotated(FOFTPTPParser.Fof_annotatedContext ctx) {
        Term f = (Term) visit(ctx.fof_formula());
        if (ctx.ID().getText().equals("conjecture")) {
            formulas.add(Term.mkNot(f));
        }
        else {
            formulas.add(f);
        }
        return null;
    }

    @Override
    public Term visitInclude(FOFTPTPParser.IncludeContext ctx) {
        String inputFilePath = ctx.SINGLE_QUOTED().getText();
        // remove the surrounding single quotes
        inputFilePath = inputFilePath.substring(1, inputFilePath.length() - 1);
        // there is a danger here with infinite includes
        // but let's assume that won't happen
        Theory thy2;
        try {
            File f = new File(filePath);
            String root_directory = f.getParentFile().getParentFile().getParent();
            File f_include = new File(root_directory + "/" + inputFilePath);
            FileInputStream fileStream = new FileInputStream(f_include);
            TptpFofParser parser = new TptpFofParser();
            Either<Errors.ParserError, Theory> result = parser.parse(fileStream);
            if (result.isLeft()) {
                errorMessage = Optional.of("Something bad happened when parsing the imported file: " + inputFilePath);
            }
            thy2 = result.right().getOrElse(null);
        } catch (Exception e) {
            errorMessage = Optional.of("couldn't process include statement: " + inputFilePath);
            return null;
        }
        // add the returned theory to the theory being built here
        // no need to add universal sort again

        // note that scala attributes are accessed as java methods
        // Add function declarations
        theory = theory.withFunctionDeclarations(thy2.functionDeclarations());

        // Add constants
        theory = theory.withConstants(thy2.constants());

        // Add axioms
        theory = theory.withAxioms(thy2.axioms());

        return null;
    }

    @Override
    public Term visitNot(FOFTPTPParser.NotContext ctx) {
        Term formula = (Term) visit(ctx.fof_formula());
        return Term.mkNot(formula);
    }

    @Override
    public Term visitForall(FOFTPTPParser.ForallContext ctx) {
        List<AnnotatedVar> variables = new ArrayList<>();
        for(TerminalNode variableNode: ctx.ID()) {
            String name = variableNode.getText();
            variables.add(Term.mkVar(name).of(universeSort));
        }
        Term body = (Term) visit(ctx.fof_formula());
        return Term.mkForall(variables, body);
    }

    @Override
    public Term visitExists(FOFTPTPParser.ExistsContext ctx) {
        List<AnnotatedVar> variables = new ArrayList<>();
        for (TerminalNode variableNode: ctx.ID()) {
            String name = variableNode.getText();
            variables.add(Term.mkVar(name).of(universeSort));
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
    public Term visitOr(FOFTPTPParser.OrContext ctx) {
        Term left = (Term) visit(ctx.fof_formula(0));
        Term right = (Term) visit(ctx.fof_formula(1));
        return Term.mkOr(left, right);
    }

    @Override
    public Term visitImp(FOFTPTPParser.ImpContext ctx) {
        Term left = (Term) visit(ctx.fof_formula(0));
        Term right = (Term) visit(ctx.fof_formula(1));
        return Term.mkImp(left, right);
    }

    @Override
    public Term visitIff(FOFTPTPParser.IffContext ctx) {
        Term left = (Term) visit(ctx.fof_formula(0));
        Term right = (Term) visit(ctx.fof_formula(1));
        return Term.mkEq(left, right);
    }

    @Override
    public Term visitEq(FOFTPTPParser.EqContext ctx) {
        Term left = (Term) visit(ctx.term(0));
        Term right = (Term) visit(ctx.term(1));
        return Term.mkEq(left, right);
    }

    @Override
    public Term visitNeq(FOFTPTPParser.NeqContext ctx) {
        Term left = (Term) visit(ctx.term(0));
        Term right = (Term) visit(ctx.term(1));
        return Term.mkNot(Term.mkEq(left, right));
    }

    @Override
    public Term visitProp(FOFTPTPParser.PropContext ctx) {
        String name = ctx.ID().getText();
        Var v = Term.mkVar(name);
        primePropositions.add(v);
        return v;
    }

    @Override
    public Term visitDefined_prop(FOFTPTPParser.Defined_propContext ctx) {
        String name = ctx.DEFINED_PROP().getText();
        if(name.equals("$true"))
            return Term.mkTop();
        else if(name.equals("$false"))
            return Term.mkBottom();
        return null;
    }

    @Override
    public Term visitPred(FOFTPTPParser.PredContext ctx) {
        String name = ctx.ID().getText();
        int numArgs = ctx.term().size();

        List<Sort> argSorts = new ArrayList<>();
        List<Term> arguments = new ArrayList<>();
        for(int i = 0; i < numArgs; i++) {
            Term ti = (Term) visit(ctx.term(i));
            arguments.add(ti);
            argSorts.add(universeSort);
        }
        
        // Remember what function signature we encountered
        FuncDecl p = FuncDecl.mkFuncDecl(name, argSorts, Sort.Bool());
        functionDeclarations.add(p);
        
        return Term.mkApp(name, arguments);
    }

    @Override
    public Term visitParen(FOFTPTPParser.ParenContext ctx) {
        return (Term) visit(ctx.fof_formula());
    }

    @Override
    public Term visitConVar(FOFTPTPParser.ConVarContext ctx) {
        String name = ctx.ID().getText();
        return Term.mkVar(name);
    }

    @Override
    public Term visitApply(FOFTPTPParser.ApplyContext ctx) {
        String name = ctx.ID().getText();
        int numArgs = ctx.term().size();
        
        List<Sort> argSorts = new ArrayList<>();
        List<Term> arguments = new ArrayList<>();
        for(int i = 0; i < numArgs; i++) {
            Term ti = (Term) visit(ctx.term(i));
            arguments.add(ti);
            argSorts.add(universeSort);
        }
        
        // Remember what function signature we encountered
        FuncDecl f = FuncDecl.mkFuncDecl(name, argSorts, universeSort);
        functionDeclarations.add(f);
        
        return Term.mkApp(name, arguments);
    }
}
