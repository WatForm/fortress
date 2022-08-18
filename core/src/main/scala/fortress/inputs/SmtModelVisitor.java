package fortress.inputs;

import java.io.*;

import fortress.msfol.*;
import fortress.operations.TermOps;
import fortress.interpretation.*;

import java.util.*;
import java.util.stream.Collectors;
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

    public SmtModelVisitor() {
        this.interpretation = BasicInterpretation.empty();
        this.functionDefinitions = new HashSet<>();
    }

    public Interpretation getItp() {
        return interpretation;
    }

    public Set<FunctionDefinition> getFunctionDefinitions() {
        return functionDefinitions;
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
        // create empty function definition
        scala.collection.immutable.Set<AnnotatedVar> args = new scala.collection.immutable.HashSet<>();

        int sorted_var_num = ctx.sorted_var().size();

        for (int i = 0; i < sorted_var_num; i++) {
            args.$plus(visitSorted_var(ctx.sorted_var(i)));
        }
        Sort resultSort = (Sort)visit(ctx.sort());
        Term body = (Term)visit(ctx.term());
        // transfer java.util.Set to scala.util.Set
        this.functionDefinitions.add(new FunctionDefinition(name, args, resultSort, body));
        return null;
    }

}


