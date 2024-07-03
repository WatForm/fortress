import org.scalatest._

import fortress.msfol._
import fortress.msfol.Term._
import fortress.msfol.Sort._
import fortress.modelfinders._
import fortress.transformers._
import fortress.solvers._
import fortress.interpretation._

import scala.util.Using

class ModelFinderProcessBuilderTest extends UnitSuite {
    test("model with integers"){
        val x = mkVar("x")
        val theory: Theory = Theory.empty
            .withSort(IntSort)
            .withConstantDeclaration(x of IntSort)
            .withAxiom(mkEq(x, IntegerLiteral(123)))
        
        val sortInterpretations: Map[Sort, Seq[Value]] = Map()
        val constantInterpretations: Map[AnnotatedVar, Value] = Map(
            (x of IntSort) -> IntegerLiteral(123)
        )
        val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map()
        
        testCVC4(theory, Map(), sortInterpretations, constantInterpretations, functionInterpretations)
        testZ3(theory, Map(), sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    test("model with bool"){
        val x = mkVar("x")
        val theory: Theory = Theory.empty
            .withConstantDeclaration(x of BoolSort)
            .withAxiom(mkEq(x, mkTop))
            
        val sortInterpretations: Map[Sort, Seq[Value]] = Map()
        val constantInterpretations: Map[AnnotatedVar, Value] = Map(
            (x of BoolSort) -> mkTop
        )
        val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map()
        
        testCVC4(theory, Map(), sortInterpretations, constantInterpretations, functionInterpretations)
        testZ3(theory, Map(), sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    test("model with bitvector"){
        val x = mkVar("x")
        val theory: Theory = Theory.empty
            .withConstantDeclaration(x of BitVectorSort(32))
            .withAxiom(mkEq(x, BitVectorLiteral(0x12345678, 32)))
            
        val sortInterpretations: Map[Sort, Seq[Value]] = Map()
        val constantInterpretations: Map[AnnotatedVar, Value] = Map(
            (x of BitVectorSort(32)) -> BitVectorLiteral(0x12345678, 32)
        )
        val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map()
        
        testCVC4(theory, Map(), sortInterpretations, constantInterpretations, functionInterpretations)
        testZ3(theory, Map(), sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    test("model with custom Sort"){
        val S = mkSortConst("S")
        val x = mkVar("x")
        val theory: Theory = Theory.empty
            .withSort(S)
            .withConstantDeclaration(x of S)
            .withAxiom(mkEq(x, mkDomainElement(1, S)))
            
        val sortInterpretations: Map[Sort, Seq[Value]] = Map(
            S -> Seq(mkDomainElement(1, S))
        )
        val constantInterpretations: Map[AnnotatedVar, Value] = Map(
            (x of S) -> mkDomainElement(1, S)
        )
        val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map()
        
        val scopes: Map[Sort, Int] = Map(S -> 1)
        
        testCVC4(theory, scopes, sortInterpretations, constantInterpretations, functionInterpretations)
        testZ3(theory, scopes, sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    test("model with function"){
        val S = mkSortConst("S")
        val x = mkVar("x")
        val y = mkVar("y")
        
        val f = FuncDecl.mkFuncDecl("f", S, BitVectorSort(16));
        
        val theory: Theory = Theory.empty
            .withSort(S)
            .withConstantDeclarations(x of S, y of S)
            .withFunctionDeclaration(f)
            .withAxiom(mkEq(x, mkDomainElement(1, S)))
            .withAxiom(mkEq(y, mkDomainElement(2, S)))
            .withAxiom(mkEq(mkApp("f", x), BitVectorLiteral(0x1234, 16)))
            .withAxiom(mkEq(mkApp("f", y), BitVectorLiteral(0xffff, 16)))
            
        val sortInterpretations: Map[Sort, Seq[Value]] = Map(
            S -> Seq(mkDomainElement(1, S), mkDomainElement(2, S))
        )
        val constantInterpretations: Map[AnnotatedVar, Value] = Map(
            (x of S) -> mkDomainElement(1, S),
            (y of S) -> mkDomainElement(2, S)
        )
//        val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map(
//            f -> Map(
//                Seq(mkDomainElement(1, S)) -> BitVectorLiteral(0x1234, 16),
//                Seq(mkDomainElement(2, S)) -> BitVectorLiteral(0xffff, 16)
//            )
//        )

        val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map(
            f -> Map.empty
        )
        
        val scopes: Map[Sort, Int] = Map(S -> 2)
        
        testCVC4(theory, scopes, sortInterpretations, constantInterpretations, functionInterpretations)
        testZ3(theory, scopes, sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    def testCVC4(theory: Theory,
        scopes: Map[Sort, Int],
        sortInterpretations: Map[Sort, Seq[Value]],
        constantInterpretations: Map[AnnotatedVar, Value],
        functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]): Unit = {
        
        testSolver(new CVC4CliSolver(), theory, scopes, sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    def testZ3(theory: Theory,
        scopes: Map[Sort, Int],
        sortInterpretations: Map[Sort, Seq[Value]],
        constantInterpretations: Map[AnnotatedVar, Value],
        functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]): Unit = {
        
        testSolver(new Z3NonIncCliSolver(), theory, scopes, sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    def testSolver(
        solver: Solver,
        theory: Theory,
        scopes: Map[Sort, Int],
        sortInterpretations: Map[Sort, Seq[Value]],
        constantInterpretations: Map[AnnotatedVar, Value],
        functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]): Unit = {
            
        Using.resource(new JoeTWOModelFinder()) { finder => {
            finder setTheory theory
            finder setSolver solver
            for ((sort, size) <- scopes) {
                finder.setExactScope(sort, size)
            }
            finder.checkSat(false) should be (ModelFinderResult.Sat)
            assertModel(finder.viewModel(), sortInterpretations, constantInterpretations, functionInterpretations)
        }}
    }
    
    def assertModel(model: Interpretation,
        sortInterpretations: Map[Sort, Seq[Value]],
        constantInterpretations: Map[AnnotatedVar, Value],
        functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]): Unit = {
        
        for((sort, values) <- model.sortInterpretations){
            values should contain theSameElementsAs sortInterpretations(sort)
        }
        model.constantInterpretations should be (constantInterpretations)
        model.functionInterpretations should be (functionInterpretations)
    }
}
