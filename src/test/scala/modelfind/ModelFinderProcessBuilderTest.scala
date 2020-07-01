import org.scalatest._

import fortress.msfol._
import fortress.msfol.Term._
import fortress.msfol.Sort._
import fortress.modelfind._
import fortress.transformers._
import fortress.solverinterface._
import fortress.interpretation._

class ModelFinderProcessBuilderTest extends UnitSuite {
    test("model with integers"){
        val x = mkVar("x")
        val theory: Theory = Theory.empty
            .withSort(IntSort)
            .withConstant(x of IntSort)
            .withAxiom(mkEq(x, IntegerLiteral(123)))
        
        val sortInterpretations: Map[Sort, Seq[Value]] = Map()
        val constantInterpretations: Map[AnnotatedVar, Value] = Map(
            (x of IntSort) -> IntegerLiteral(123)
        )
        val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map()
        
        testCVC4(theory, sortInterpretations, constantInterpretations, functionInterpretations)
        testZ3(theory, sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    test("model with bool"){
        val x = mkVar("x")
        val theory: Theory = Theory.empty
            .withConstant(x of BoolSort)
            .withAxiom(mkEq(x, mkTop))
            
        val sortInterpretations: Map[Sort, Seq[Value]] = Map()
        val constantInterpretations: Map[AnnotatedVar, Value] = Map(
            (x of BoolSort) -> mkTop
        )
        val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map()
        
        testCVC4(theory, sortInterpretations, constantInterpretations, functionInterpretations)
        testZ3(theory, sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    test("model with bitvector"){
        val x = mkVar("x")
        val theory: Theory = Theory.empty
            .withConstant(x of BitVectorSort(32))
            .withAxiom(mkEq(x, BitVectorLiteral(0x12345678, 32)))
            
        val sortInterpretations: Map[Sort, Seq[Value]] = Map()
        val constantInterpretations: Map[AnnotatedVar, Value] = Map(
            (x of BitVectorSort(32)) -> BitVectorLiteral(0x12345678, 32)
        )
        val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map()
        
        testCVC4(theory, sortInterpretations, constantInterpretations, functionInterpretations)
        testZ3(theory, sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    test("model with custom Sort"){
        val S = mkSortConst("S")
        val x = mkVar("x")
        val theory: Theory = Theory.empty
            .withSort(S)
            .withConstant(x of S)
            .withAxiom(mkEq(x, mkDomainElement(1, S)))
            
        val sortInterpretations: Map[Sort, Seq[Value]] = Map(
            S -> Seq(mkDomainElement(1, S))
        )
        val constantInterpretations: Map[AnnotatedVar, Value] = Map(
            (x of S) -> mkDomainElement(1, S),
            (Var("$1S") of S) -> mkDomainElement(1, S)
        )
        val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map()
        
        val finder = new FortressTWO(new CVC4CliSolver)
        finder setTheory theory
        finder.setAnalysisScope(S, 1)
        finder.checkSat should be (ModelFinderResult.Sat)
        assertModel(finder.viewModel(), sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    def testCVC4(theory: Theory,
        sortInterpretations: Map[Sort, Seq[Value]],
        constantInterpretations: Map[AnnotatedVar, Value],
        functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]): Unit = {
        
        testSolverStrategy(new CVC4CliSolver, theory, sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    def testZ3(theory: Theory,
        sortInterpretations: Map[Sort, Seq[Value]],
        constantInterpretations: Map[AnnotatedVar, Value],
        functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]): Unit = {
        
        testSolverStrategy(new Z3CliSolver, theory, sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    def testSolverStrategy(
        strategy: SolverStrategy,
        theory: Theory,
        sortInterpretations: Map[Sort, Seq[Value]],
        constantInterpretations: Map[AnnotatedVar, Value],
        functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]): Unit = {
            
        val finder = new FortressTWO(strategy)
        finder setTheory theory
        finder.checkSat should be (ModelFinderResult.Sat)
        assertModel(finder.viewModel(), sortInterpretations, constantInterpretations, functionInterpretations)
    }
    
    def assertModel(model: Interpretation,
        sortInterpretations: Map[Sort, Seq[Value]],
        constantInterpretations: Map[AnnotatedVar, Value],
        functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]]): Unit = {
        
        model.sortInterpretations should be (sortInterpretations)
        model.constantInterpretations should be (constantInterpretations)
        model.functionInterpretations should be (functionInterpretations)
    }
}
