package fortress.inputs;

import java.io.*;

import fortress.msfol.*;
import fortress.operations.TermOps;
import fortress.interpretation.*;

import java.util.*;
import java.util.stream.Collectors;

import fortress.util.Errors;
import fortress.util.NameConverter;
import org.antlr.v4.runtime.tree.ParseTree;
import scala.collection.JavaConverters.*;

import org.antlr.v4.runtime.misc.Interval;
import scala.collection.Seq;

import java.lang.Void;

/*
  (define-fun faa ((x!0 P)) H
    (ite (= x!0 P!val!0) H!val!1
      H!val!0))
 */

public class SmtModelVisitor extends SmtLibVisitor{

    private Signature signature;
//    private Set<AnnotatedVar> constants;
//    private Map<Sort, Scope> scopeMap;
//    private Interpretation interpretation;
//    private Map<Sort, Seq<Value>> sortInterpretations;
//    private Map<AnnotatedVar, Value> constantInterpretations;
    private Set<FunctionDefinition> functionDefinitions;

    private Map<String, DomainElement> smtValue2DomainElement = new HashMap<>();

    private Map<String, String> fortressName2SmtValue = new HashMap<>();

    String pattern = ".+!val![0-9]*$";



    public SmtModelVisitor(Signature signature) {
        this.signature = signature;
//        this.constants = (Set<AnnotatedVar>) this.signature.constants();
//        this.scopeMap = scopeMap;
//        this.sortInterpretations = new HashMap<>();
//        this.constantInterpretations = new HashMap<>();
        this.functionDefinitions = new HashSet<>();
    }


    public Set<FunctionDefinition> getFunctionDefinitions() {
        return functionDefinitions;
    }
    public Map<String, String> getFortressName2SmtValue() { return fortressName2SmtValue; }
    public Map<String, DomainElement> getSmtValue2DomainElement() { return smtValue2DomainElement; }

    @Override
    public Void visitDeclare_fun(SmtLibSubsetParser.Declare_funContext ctx) {
        // '(' 'declare-fun' ID '(' sort* ')' sort ')'    # declare_fun
        assert ctx.sort().size()==1 : "There shouldn't be more than one sort in the declare-fun of return smt model.";
        Sort sort = (Sort)visit(ctx.sort(0));
        String name = ctx.ID().getText();   //     H!val!0
        assert name.matches(pattern): "Parse error, exit code: 1";
        String[] temp = name.split("!val!");   // "H!val!0" => "H" "0"
        assert temp.length == 2: "Parse error, exit code: 2";
        assert temp[0].equals(sort.name()): "Parse error, exit code: 3";
        DomainElement domainElement = Term.mkDomainElement(Integer.parseInt(temp[1])+1, sort);
        this.smtValue2DomainElement.put(name, domainElement);
        this.fortressName2SmtValue.put(domainElement.toString(), name);
        return null;
    }


    @Override
    public Term visitVar(SmtLibSubsetParser.VarContext ctx) {
        String varName = ctx.getText();
        if(smtValue2DomainElement.containsKey(varName)) {
            varName = this.smtValue2DomainElement.get(varName).toString();
            return DomainElement.interpretName(varName).get();
        }
        return Term.mkVar(varName);
    }

    @Override
    public AnnotatedVar visitSorted_var(SmtLibSubsetParser.Sorted_varContext ctx) {
        String name = ctx.ID().getText();
        Var var = Term.mkVar(name);
        Sort sort = (Sort)visit(ctx.sort());
        return new AnnotatedVar(var, sort);
    }

    @Override
    public Void visitDefine_fun(SmtLibSubsetParser.Define_funContext ctx) {
        //'(' 'define-fun' ID '(' sorted_var* ')' sort term ')'
        String name = ctx.ID().getText();
        // faa -> f
        name = NameConverter.nameWithoutAffix(name);
        int argNum = ctx.sorted_var().size();
//        Set<AnnotatedVar> args = new HashSet<>();
        List<AnnotatedVar> args = new ArrayList<>();
        for(int i=0; i<argNum; i++) {
            args.add( visitSorted_var( ctx.sorted_var(i) ) );
        }
        Sort resultSort = (Sort)visit(ctx.sort());
        Term body = (Term)visit(ctx.term());
        this.functionDefinitions.add(FunctionDefinition.mkFunctionDefinition(name, args, resultSort, body));
        this.fortressName2SmtValue.put(name, body.toString());
        return null;
    }

}


