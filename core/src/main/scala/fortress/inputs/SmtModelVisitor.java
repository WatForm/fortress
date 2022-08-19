package fortress.inputs;

import java.io.*;

import fortress.msfol.*;
import fortress.operations.TermOps;
import fortress.interpretation.*;

import java.util.*;
import java.util.stream.Collectors;

import org.antlr.v4.runtime.tree.ParseTree;
import scala.collection.JavaConverters.*;

import org.antlr.v4.runtime.misc.Interval;

import java.lang.Void;

/*
  (define-fun faa ((x!0 P)) H
    (ite (= x!0 P!val!0) H!val!1
      H!val!0))
 */

public class SmtModelVisitor extends SmtLibVisitor{
    private Interpretation interpretation;
    private Set<FunctionDefinition> functionDefinitions = null;

    private Map<String, DomainElement> smtValueToDomainElement;

    public SmtModelVisitor(Map<String, DomainElement> smtValueToDomainElement) {
        this.interpretation = BasicInterpretation.empty();
        this.functionDefinitions = new HashSet<>();
        this.smtValueToDomainElement = smtValueToDomainElement;
        System.out.println("smtValueToDomainElement: " + smtValueToDomainElement);
    }

    public Interpretation getItp() {
        return interpretation;
    }

    public Set<FunctionDefinition> getFunctionDefinitions() {
        return functionDefinitions;
    }


    @Override
    public Term visitVar(SmtLibSubsetParser.VarContext ctx) {
        String varName = ctx.getText();
        if(smtValueToDomainElement.containsKey(varName)) {
            varName = this.smtValueToDomainElement.get(varName).toString();
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
    public Void visitFunction_def(SmtLibSubsetParser.Function_defContext ctx) {
        String name = ctx.ID().getText(); // function name
        // arg list, ex: a:A
        Set<AnnotatedVar> args = new HashSet<>();
        int sorted_var_num = ctx.sorted_var().size();
        for (int i = 0; i < sorted_var_num; i++) {
            args.add(visitSorted_var(ctx.sorted_var(i)));
        }
        // save return type as a Sort
        Sort resultSort = (Sort)visit(ctx.sort());
        // save function body as a term
        Term body = (Term)visit(ctx.term());
        // transfer java.util.Set to scala.util.Set
        this.functionDefinitions.add(FunctionDefinition.mkFunctionDefinition(name, args, resultSort, body));
        return null;
    }

}


