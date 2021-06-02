import org.scalatest._

import fortress.msfol._
import fortress.interpretation._

class EvaluationBasedInterpretationTest extends UnitSuite {
    val A = Sort.mkSortConst("A")
    val c = Var("c")
    val f = FuncDecl("f", A, A)
    
    val signature = Signature.empty
        .withSort(A)
        .withConstant(c of A)
        .withFunctionDeclaration(f)
    
    test("create interpretation") {
        object Interp extends EvaluationBasedInterpretation(signature) {
            def evaluateSort(s: Sort): Seq[Value] = s match {
                case `A` => DomainElement.range(1 to 5, A)
                case _ => fail("Unexpected sort: " + s.toString)
            }
            
            def evaluateConstant(const: AnnotatedVar): Value = const match {
                case AnnotatedVar(Var("c"), A) => DomainElement(3, A)
                case _ => fail("Unexpected constant: " + c.toString)
            }
            
            def evaluateFunction(func: FuncDecl, argList: Seq[Value]): Value = (func, argList) match {
                case (`f`, Seq(DomainElement(1, A))) => DomainElement(2, A) 
                case (`f`, Seq(DomainElement(2, A))) => DomainElement(3, A) 
                case (`f`, Seq(DomainElement(3, A))) => DomainElement(4, A) 
                case (`f`, Seq(DomainElement(4, A))) => DomainElement(5, A) 
                case (`f`, Seq(DomainElement(5, A))) => DomainElement(1, A) 
                case _ => fail("Unexpected (func, argList) pair: " + (func, argList).toString)
            } 
        }
        
        Interp.constantInterpretations should be (Map(
            (c of A) -> DomainElement(3, A)
        ))
        
        Interp.sortInterpretations should be (Map(
            A -> DomainElement.range(1 to 5, A)
        ))
        
        Interp.functionInterpretations should be (Map(f -> Map(
            Seq(DomainElement(1, A)) -> DomainElement(2, A),
            Seq(DomainElement(2, A)) -> DomainElement(3, A),
            Seq(DomainElement(3, A)) -> DomainElement(4, A),
            Seq(DomainElement(4, A)) -> DomainElement(5, A),
            Seq(DomainElement(5, A)) -> DomainElement(1, A)
        )))
    }
}