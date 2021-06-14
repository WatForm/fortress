package fortress.inputs;

import org.antlr.v4.runtime.tree.TerminalNode;

import fortress.msfol.*;

import java.util.List;
import java.io.*;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;
import java.util.stream.Collectors;

import scala.jdk.javaapi.CollectionConverters;

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
    private Boolean noParseError = true;

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

    public Theory getTheory() {
        if (noParseError) return theory;
        else return null;
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
        for(FuncDecl f : functionDeclarations) {
            theory = theory.withFunctionDeclaration(f);
        }
        
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
        for(Term formula : formulas) {
            theory = theory.withAxiom(formula);
        }
        
        return null;
    }

    // Add formulas as axioms, or if the formula is a conjecture, add its negation
    @Override
    public Term visitFof_annotated(FOFTPTPParser.Fof_annotatedContext ctx) {
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
    public Term visitInclude(FOFTPTPParser.IncludeContext ctx) {
        String inputFilePath = ctx.SINGLE_STRING().getText();
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
            thy2 = parser.parse(fileStream);
        } catch (Exception e) {
            System.err.println("couldn't process include statement: " + inputFilePath);
            noParseError = false;
            return null;
        }
        // add the returned theory to the theory being built here
        // no need to add universal sort again

        // note that scala attributes are accessed as java methods
        // Add function declarations
        for (FuncDecl fs : CollectionConverters.asJava(thy2.functionDeclarations())) {
            theory = theory.withFunctionDeclaration(fs);
        }
        // Add constants
        for (AnnotatedVar c : CollectionConverters.asJava(thy2.constants())) {
            theory = theory.withConstant(c);
        }
        // Add axioms
        for (Term ax : CollectionConverters.asJava(thy2.axioms())) {
            theory = theory.withAxiom(ax);
        }
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
