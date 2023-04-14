import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.NoOverflowBVTransformer
import fortress.config._
import fortress.problemstate._
import scala.util.Using
import fortress.util.Seconds
import fortress.modelfind.ModelFinderResult
import fortress.compiler.ConfigurableCompiler
import fortress.modelfind.SimpleModelFinder

import fortress.util.Dump

class NoOverflowBVTransformerTests extends UnitSuite with CommonSymbols {
    
    val BV4 = BitVectorSort(4)
    val zero4 = BitVectorLiteral(0, 4)

    val manager = Manager.makeEmpty()
      manager.addOption(TypecheckSanitizeOption, 1)
      manager.addOption(EnumEliminationOption, 2)
      manager.addOption(QuantifierExpansionOption, 5001)
      manager.addOption(RangeFormulaOption, 5002)
      manager.addOption(SimplifyOption, 5003)
      manager.addOption(DatatypeOption, 5004)

    val managerWithOverflow = Manager.makeEmpty()
      managerWithOverflow.addOption(TypecheckSanitizeOption, 1)
      managerWithOverflow.addOption(EnumEliminationOption, 2)
      managerWithOverflow.addOption(new ConfigOption("NoBVOverflow", _.addTransformer(NoOverflowBVTransformer)))
      managerWithOverflow.addOption(QuantifierExpansionOption, 5001)
      managerWithOverflow.addOption(RangeFormulaOption, 5002)
      // managerWithOverflow.addOption(SimplifyOption, 5003)
      managerWithOverflow.addOption(DatatypeOption, 5004)


    def ensureUnsat(theory: Theory) {
      Using.resource(managerWithOverflow.setupModelFinder()) {
        finder => {
          finder.setTheory(theory)
          finder.setTimeout(Seconds(10))
          val result = finder.checkSat()

          if (result == ModelFinderResult.Sat) {
                    val modelstring = finder.viewModel().toString()
                    println(modelstring)
          }
          result shouldBe (ModelFinderResult.Unsat)
          //assert(result == ModelFinderResult.Unsat)
        }
      }
    }

    def ensureSat(theory: Theory) {
      Using.resource(managerWithOverflow.setupModelFinder()) {
        finder => {
          finder.setTheory(theory)
          finder.setTimeout(Seconds(10))
          val result = finder.checkSat()
          result shouldBe (ModelFinderResult.Sat)
          //assert(result == ModelFinderResult.Sat)
        }
      }
    }

    def printConverted(theory: Theory, scopes: Map[Sort, Scope] = Map.empty){
      val compiler = managerWithOverflow.setupCompiler()
      compiler.compile(theory, scopes, Seconds(10).toMilli, Seq.empty) match {
        case Left(_) => ()
        case Right(result) => println(result.theory)
      }
    }

    test("addition wrapped") {

        val core = BuiltinApp(BvSignedLE,BuiltinApp(BvPlus, x1, x2), BitVectorLiteral(7, 4))
        
        val axiom = Not(core)
        
        val expectedCheck = Or(
            And(
              BuiltinApp(BvSignedGT, x1, zero4), 
              BuiltinApp(BvSignedGT, x2, zero4),
              Not(BuiltinApp(BvSignedGT, BuiltinApp(BvPlus, x1, x2), zero4))
            ),
            And(
              BuiltinApp(BvSignedLT, x1, zero4), 
              BuiltinApp(BvSignedLT, x2, zero4),
              Not(BuiltinApp(BvSignedLT, BuiltinApp(BvPlus, x1, x2), zero4))
            )
          )
        // double negated check due to how the polarity is applied.
        // Could likely be streamlined later
        val expectedAxiom = Not(Or(core, expectedCheck))


        val theory = Theory.empty
        .withConstantDeclarations(x1 of BV4, x2 of BV4)
        .withAxiom(axiom)

        val initialState = ProblemState(theory)
        


        val expected = Theory.empty
            .withConstantDeclarations(x1 of BV4, x2 of BV4)
            .withAxiom(expectedAxiom)

        val transformer: NoOverflowBVTransformer = NoOverflowBVTransformer
        val result = transformer(ProblemState(theory))

        //result.theory.axioms.toSeq(0) should be (expectedAxiom)

        result should be (ProblemState(expected))

        ensureUnsat(result.theory)

    }

    test("addition no overflow") {

      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4, x3 of BV4)
      .withAxioms(Seq(
        BuiltinApp(BvSignedGT, x1, zero4),
        BuiltinApp(BvSignedGT, x2, zero4),
        Eq(BuiltinApp(BvPlus, x1, x2), x3),
        BuiltinApp(BvSignedLE, x3, zero4)
      ))

      ensureUnsat(theory)

    }

    test("addition no weirdness"){

      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4, x3 of BV4)
      .withAxioms(Seq(
        BuiltinApp(BvSignedGT, x1, zero4),
        BuiltinApp(BvSignedGT, x2, zero4),
        Eq(BuiltinApp(BvPlus, x1, x2), x3),
        Not(BuiltinApp(BvSignedGT, x3, x1))
      ))

      ensureUnsat(theory)

    }

    test("addition no underflow") {

      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4, x3 of BV4)
      .withAxioms(Seq(
        BuiltinApp(BvSignedLT, x1, zero4),
        BuiltinApp(BvSignedLT, x2, zero4),
        Eq(BuiltinApp(BvPlus, x1, x2), x3),
        BuiltinApp(BvSignedGE, x3, zero4)
      ))

      ensureUnsat(theory)

    }

    test("subtraction no overflow"){
      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4, x3 of BV4)
      .withAxioms(Seq(
        BuiltinApp(BvSignedGT, x1, zero4),
        BuiltinApp(BvSignedLT, x2, zero4),
        Eq(BuiltinApp(BvSub, x1, x2), x3),
        BuiltinApp(BvSignedLE, x3, zero4)
      ))

      ensureUnsat(theory)
    }

    test("subtraction no underflow") {
      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4, x3 of BV4)
      .withAxioms(Seq(
        BuiltinApp(BvSignedLT, x1, zero4),
        BuiltinApp(BvSignedGT, x2, zero4),
        Eq(BuiltinApp(BvSub, x1, x2), x3),
        BuiltinApp(BvSignedGE, x3, zero4)
      ))

      ensureUnsat(theory)
    }

    test("multiplication no overflow") {
      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4, x3 of BV4)
      .withAxioms(Seq(
        BuiltinApp(BvSignedGT, x1, zero4),
        BuiltinApp(BvSignedGT, x2, zero4),
        Eq(BuiltinApp(BvMult, x1, x2), x3),
        BuiltinApp(BvSignedLT, x3, x1)
      ))

      ensureUnsat(theory)
    }

    test("multiplication no underflow") {
      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4, x3 of BV4)
      .withAxioms(Seq(
        BuiltinApp(BvSignedLT, x1, zero4),
        BuiltinApp(BvSignedLT, x2, zero4),
        Eq(BuiltinApp(BvMult, x1, x2), x3),
        BuiltinApp(BvSignedLT, x3, x1)
      ))

      ensureUnsat(theory)
    }

    test("no div 0") {
      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4)
      .withAxioms(Seq(
        Eq(BuiltinApp(BvSignedDiv, x1, zero4), x2),
      ))

      ensureUnsat(theory)
    }

    // TODO test in other structures

    test("In Or") {
      val body = Or(Eq(BuiltinApp(BvSignedDiv, x1, zero4), x1), Bottom)

      val theory = Theory.empty
      .withConstantDeclaration(x1 of BV4)
      .withAxiom(body)

      ensureUnsat(theory)

      val theoryForall = Theory.empty
      .withAxiom(Forall(x1 of BV4, body))

      ensureSat(theoryForall)
    }

    test("In And") {
      val body = And(Eq(BuiltinApp(BvSignedDiv, x1, zero4), x1), Top)

      val theory = Theory.empty
      .withConstantDeclaration(x1 of BV4)
      .withAxiom(body)

      ensureUnsat(theory)

      val theoryForall = Theory.empty
      .withAxiom(Forall(x1 of BV4, body))

      ensureSat(theoryForall)
    }

    test("In Implication Left") {
      val body = Implication(Eq(BuiltinApp(BvSignedDiv, x1, zero4), x1), Bottom)

      val theory = Theory.empty
      .withConstantDeclaration(x1 of BV4)
      .withAxiom(body)

      ensureUnsat(theory)

      val theoryForall = Theory.empty
      .withAxiom(Forall(x1 of BV4, body))

      ensureSat(theoryForall)
    }

    test("In Implication Right") {
      val body = Implication(Top, Eq(BuiltinApp(BvSignedDiv, x1, zero4), x1))

      val theory = Theory.empty
      .withConstantDeclaration(x1 of BV4)
      .withAxiom(body)

      ensureUnsat(theory)

      val theoryForall = Theory.empty
      .withAxiom(Forall(x1 of BV4, body))

      ensureSat(theoryForall)
    }

    test("In Iff vs True"){
      val bodyTrue = Iff(Eq(BuiltinApp(BvSignedDiv, x1, zero4), x1), Top)

      val theoryTrue = Theory.empty
      .withConstantDeclaration(x1 of BV4)
      .withAxiom(bodyTrue)

      ensureUnsat(theoryTrue)

      val theoryForallTrue = Theory.empty
      .withAxiom(Forall(x1 of BV4, bodyTrue))
      ensureSat(theoryForallTrue)
    }

    test("In Iff vs False"){
      val bodyFalse = Iff(Eq(BuiltinApp(BvSignedDiv, x1, zero4), x1), Bottom)

      val theoryFalse = Theory.empty
      .withConstantDeclaration(x1 of BV4)
      .withAxiom(bodyFalse)

      /*
      val compiler = managerWithOverflow.setupCompiler()
      compiler.compile(theoryFalse, Map.empty, Seconds(10).toMilli, Seq.empty) match {
        case Left(_) => "Failed to compile"
        case Right(res) => println(res.theory.toString()); println("=== SMT ==="); println(Dump.theoryToSmtlib(res.theory))
      }
      */
      ensureUnsat(theoryFalse)

      val theoryForallFalse = Theory.empty
      .withAxiom(Forall(x1 of BV4, bodyFalse))
      ensureSat(theoryForallFalse)
    }

    test("In Eq vs False"){
      val bodyFalse = Eq(Eq(BuiltinApp(BvSignedDiv, x1, zero4), x1), Bottom)

      val theoryFalse = Theory.empty
      .withConstantDeclaration(x1 of BV4)
      .withAxiom(bodyFalse)

      /*
      val compiler = managerWithOverflow.setupCompiler()
      compiler.compile(theoryFalse, Map.empty, Seconds(10).toMilli, Seq.empty) match {
        case Left(_) => "Failed to compile"
        case Right(res) => println(res.theory.toString()); println("=== SMT ==="); println(Dump.theoryToSmtlib(res.theory))
      }
      */
      ensureUnsat(theoryFalse)

      val theoryForallFalse = Theory.empty
      .withAxiom(Forall(x1 of BV4, bodyFalse))
      ensureSat(theoryForallFalse)
    }

    test("In Eq vs True"){
      val bodyFalse = Eq(Eq(BuiltinApp(BvSignedDiv, x1, zero4), x1), Top)

      val theoryFalse = Theory.empty
      .withConstantDeclaration(x1 of BV4)
      .withAxiom(bodyFalse)

      /*
      val compiler = managerWithOverflow.setupCompiler()
      compiler.compile(theoryFalse, Map.empty, Seconds(10).toMilli, Seq.empty) match {
        case Left(_) => "Failed to compile"
        case Right(res) => println(res.theory.toString()); println("=== SMT ==="); println(Dump.theoryToSmtlib(res.theory))
      }
      */
      ensureUnsat(theoryFalse)

      val theoryForallFalse = Theory.empty
      .withAxiom(Forall(x1 of BV4, bodyFalse))
      ensureSat(theoryForallFalse)
    }

    test("In Function arguments") {
      val f = FuncDecl("f", BV4, BV4)
      // x1 / 0 == x1
      val body = Eq(App("f", BuiltinApp(BvSignedDiv, x1, zero4)), x1)

      val theory = Theory.empty
      .withConstantDeclaration(x1 of BV4)
      .withFunctionDeclaration(f)
      .withAxiom(body)

      ensureUnsat(theory)

      val theoryForall = Theory.empty
      .withFunctionDeclaration(f)
      .withAxiom(Forall(x1 of BV4, body))

      ensureSat(theoryForall)
    }

    test("In Predicate Arguments"){
      val f = FuncDecl("f", BV4, BoolSort)
      // x1 / 0 == x1
      val body = App("f", BuiltinApp(BvSignedDiv, x1, zero4))

      val theory = Theory.empty
      .withConstantDeclaration(x1 of BV4)
      .withFunctionDeclaration(f)
      .withAxiom(body)

      ensureUnsat(theory)

      val theoryForall = Theory.empty
      .withFunctionDeclaration(f)
      .withAxiom(Forall(x1 of BV4, body))

      ensureSat(theoryForall)
    }

    test("In Distinct"){
      val body = Distinct(BuiltinApp(BvSignedDiv, x1, zero4), x2)

      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4)
      .withAxiom(body)

      ensureUnsat(theory)

      val theoryForall = Theory.empty
      .withAxiom(Forall(Seq(x1 of BV4, x2 of BV4), body))

      ensureSat(theoryForall)
    }

    /*
    TODO
    test("Nested ITE")
    */
    test("In ITE Condition"){
      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4, x3 of BV4)
      .withAxioms(Seq(
        BuiltinApp(BvSignedGT, x1, zero4),
        BuiltinApp(BvSignedGT, x2, zero4),
        // x1 + x2 <= 0
        IfThenElse(BuiltinApp(BvSignedLE, BuiltinApp(BvPlus, x1, x2), zero4), Top, Bottom)
      ))

      ensureUnsat(theory)
    }

    test("In ITE then"){
      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4, x3 of BV4)
      .withAxioms(Seq(
        BuiltinApp(BvSignedGT, x1, zero4),
        BuiltinApp(BvSignedGT, x2, zero4),
        // x1 + x2 <= 0
        IfThenElse(Eq(x3, zero4), BuiltinApp(BvSignedLE, BuiltinApp(BvPlus, x1, x2), zero4), Bottom)
      ))

      ensureUnsat(theory)
    }

    test("In ITE else"){
      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4, x3 of BV4)
      .withAxioms(Seq(
        BuiltinApp(BvSignedGT, x1, zero4),
        BuiltinApp(BvSignedGT, x2, zero4),
        // x1 + x2 <= 0
        IfThenElse(Eq(x3, zero4), Bottom, BuiltinApp(BvSignedLE, BuiltinApp(BvPlus, x1, x2), zero4))
      ))

      ensureUnsat(theory)
    }

    test("In ITE nested") {
      // Should be True except when it overflows
      val condition = IfThenElse(BuiltinApp(BvSignedLE, BuiltinApp(BvPlus, x1, x2), zero4), Bottom, Top)
      val big = IfThenElse(condition, Bottom, Top)
      val theory = Theory.empty
      .withConstantDeclarations(x1 of BV4, x2 of BV4, x3 of BV4)
      .withAxioms(Seq(
        BuiltinApp(BvSignedGT, x1, zero4),
        BuiltinApp(BvSignedGT, x2, zero4),
        big
      ))

      ensureUnsat(theory)
    }
    


}