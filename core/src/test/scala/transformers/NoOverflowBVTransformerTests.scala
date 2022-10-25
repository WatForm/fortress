import org.scalatest._

import fortress.msfol._
import fortress.transformers._
import fortress.transformers.NoOverflowBVTransformer
import fortress.config._
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
      managerWithOverflow.addOption(SimplifyOption, 5003)
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
                assert(result == ModelFinderResult.Unsat)
        }
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
        val expectedAxiom = Not(Or(core, Not(Not(expectedCheck))))


        val theory = Theory.empty
        .withConstants(x1 of BV4, x2 of BV4)
        .withAxiom(axiom)

        val initialState = ProblemState(theory)
        


        val expected = Theory.empty
            .withConstants(x1 of BV4, x2 of BV4)
            .withAxiom(expectedAxiom)

        val transformer: NoOverflowBVTransformer = NoOverflowBVTransformer
        val result = transformer(ProblemState(theory))

        //result.theory.axioms.toSeq(0) should be (expectedAxiom)

        result should be (ProblemState(expected))

        ensureUnsat(result.theory)

    }

    test("addition no overflow") {

      val theory = Theory.empty
      .withConstants(x1 of BV4, x2 of BV4, x3 of BV4)
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
      .withConstants(x1 of BV4, x2 of BV4, x3 of BV4)
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
      .withConstants(x1 of BV4, x2 of BV4, x3 of BV4)
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
      .withConstants(x1 of BV4, x2 of BV4, x3 of BV4)
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
      .withConstants(x1 of BV4, x2 of BV4, x3 of BV4)
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
      .withConstants(x1 of BV4, x2 of BV4, x3 of BV4)
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
      .withConstants(x1 of BV4, x2 of BV4, x3 of BV4)
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
      .withConstants(x1 of BV4, x2 of BV4)
      .withAxioms(Seq(
        Eq(BuiltinApp(BvSignedDiv, x1, zero4), x2),
      ))

      ensureUnsat(theory)
    }

    // TODO test in other structures

}