package fortress.inputs;

import fortress.msfol.*;

import java.util.*;

import fortress.util.NameConverter;

import java.lang.Void;


import java.util.Optional;
import static scala.jdk.javaapi.OptionConverters.toJava;

/* 
    These are the parts of SMT-LIB that appear in a
    model/instance return for a satisfiable problem
*/

/*
  (define-fun faa ((x!0 P)) H
    (ite (= x!0 P!val!0) H!val!1
      H!val!0))
 */

/*
(declare-fun P!val!0 () P)
  (declare-fun P!val!1 () P)
  ;; cardinality constraint:
  (forall ((x P)) (or (= x P!val!0) (= x P!val!1)))
  ;; -----------
  (define-fun _@3Haa () H
    H!val!2)
  (define-fun _@1Paa () P
    P!val!0)

 */

public class SmtModelVisitor extends SmtLibVisitor{

    private Signature signature;
    private Set<FunctionDefinition> functionDefinitions;

    // H!val!0 -> _@1Haa
    private Map<String, DomainElement> smtValue2DomainElement = new HashMap<>();

    private Map<String, String> fortressName2SmtValue = new HashMap<>();

    // This is the pattern of a DE from Z3
    String z3PatternDE = ".+!val![0-9]*$";

    // This is the pattern of a DE from CVC5
    String cvc5PatternDE = "^\\(as ?@\\S+ ?\\S+\\)$";

    public SmtModelVisitor(Signature signature) {
        this.signature = signature;
        this.functionDefinitions = new HashSet<>();
    }

    public Set<FunctionDefinition> getFunctionDefinitions() {
        return functionDefinitions;
    }
    public Map<String, String> getFortressName2SmtValue() { return fortressName2SmtValue; }
    public Map<String, DomainElement> getSmtValue2DomainElement() { return smtValue2DomainElement; }

    // NAD: is this used?  Are there declared functions in a returned instances from an SMT solver?
    @Override
    public Void visitDeclare_fun(SmtLibSubsetParser.Declare_funContext ctx) {
        // '(' 'declare-fun' ID '(' sort* ')' sort ')'    # declare_fun
        assert ctx.sort().size()==1 : "There shouldn't be more than one sort in the declare-fun of return smt model.";
        Sort sort = (Sort)visit(ctx.sort(0));
        String name = NameConverter.nameWithoutQuote(ctx.ID().getText());   //     H!val!0 (If function is quoted, the entire val thing is too)
        assert name.matches(z3PatternDE): "Parse error, exit code: 1"; // declare-fun is not used in CVC5 output
        String[] temp = name.split("!val!");   // "H!val!0" => "H" "0"
        //assert temp.length == 2: "Parse error, exit code: 2";
        //assert temp[0].equals(sort.name()): "Parse error, exit code: 3"; // "H"
        if (temp.length == 2) {
            DomainElement domainElement = Term.mkDomainElement(Integer.parseInt(temp[1])+1, sort);
            this.smtValue2DomainElement.put(name, domainElement);
            return null;
        } else {

        }
        //System.out.println("Name: " + name);
        //System.out.println("Temp: " + temp.length);
//        this.fortressName2SmtValue.put(domainElement.toString(), name);
        return null;
    }


    @Override
    public Term visitVar(SmtLibSubsetParser.VarContext ctx) {
        String varName = ctx.getText();
        varName = NameConverter.nameWithoutQuote(varName);
        
        Optional<DomainElement> oDomainValue = toJava(DomainElement.interpretName(varName));
        if (oDomainValue.isPresent()){
            return oDomainValue.get();
        }
//        if(smtValue2DomainElement.containsKey(varName)) {
//            varName = this.smtValue2DomainElement.get(varName).toString();
//            return DomainElement.interpretName(varName).get();
//        }
        return Term.mkVar(varName);
    }

    @Override
    public AnnotatedVar visitSorted_var(SmtLibSubsetParser.Sorted_varContext ctx) {
        String name = NameConverter.nameWithoutQuote(ctx.ID().getText());
        Var var = Term.mkVar(name);
        Sort sort = (Sort)visit(ctx.sort());
        return new AnnotatedVar(var, sort);
    }

    @Override
    public Void visitDefine_fun(SmtLibSubsetParser.Define_funContext ctx) {
        //'(' 'define-fun' ID '(' sorted_var* ')' sort term ')'
        String name = ctx.ID().getText();
        // faa -> f
        name = NameConverter.nameWithoutQuote(name);
        int argNum = ctx.sorted_var().size();
//        Set<AnnotatedVar> args = new HashSet<>();
        List<AnnotatedVar> args = new ArrayList<>();
        for(int i=0; i<argNum; i++) {
            args.add( visitSorted_var( ctx.sorted_var(i) ) );
        }
        Sort resultSort = (Sort)visit(ctx.sort());

        String funcBody = ctx.term().getText();
        
        // For Z3: if function body is a |-quoted var, drop the quotes
        if (funcBody.matches(z3PatternDE)){
            funcBody = NameConverter.nameWithoutQuote(funcBody);
        }

        // For CVC5: function body is an as-term, so remove any quotes from variables in it
        if (funcBody.matches(cvc5PatternDE)) {
            funcBody = NameConverter.removeAllQuotes(funcBody);
        }

//        System.out.println("funcbody: " + funcBody);

//        if( smtValue2DomainElement.containsKey(funcBody) ) {  // H!val!0
            if(name.startsWith("_@")) { // _@1H
                DomainElement de = DomainElement.interpretName(name).get();
                smtValue2DomainElement.put(funcBody, de);
            }
//        }

//        if( smtValue2DomainElement.containsKey(funcBody)) {
//            DomainElement value = smtValue2DomainElement.get(funcBody);
//            for( Map.Entry<String, DomainElement> entry : smtValue2DomainElement.entrySet()) {
//                String key = entry.getKey();
//                DomainElement de = entry.getValue();
//                if( de.toString().equals(name) ) {
////                    System.out.println("debug* : " + name);
//                    smtValue2DomainElement.put(funcBody, de);
//                    smtValue2DomainElement.put( key, value );
////                    System.out.println("@@@: " + funcBody + " ==> " + de.toString());
//                    break;
//                }
//            }
//        }

        Term body = (Term)visit(ctx.term());
        this.functionDefinitions.add(FunctionDefinition.mkFunctionDefinition(name, args, resultSort, body));
        this.fortressName2SmtValue.put(name, funcBody);
        return null;
    }

    @Override
    public Term visitAs_domain_element(SmtLibSubsetParser.As_domain_elementContext ctx) {
        // (as @Sort_this/Train_0_0 Sort_this/Train_0) for a domain element in CVC5

        // HACK: The smt-value system is quite generic and can handle any kind of term that the smt solver uses to
        // represent an atom by converting it to string by getText(). However, references to smt-values are expected to
        // be Vars containing the getText(), so just generate a Var of that form.
        return Term.mkVar(NameConverter.removeAllQuotes(ctx.getText()));
    }
}


