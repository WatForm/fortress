import java.io.{File, FileInputStream}

import fortress.inputs.SmtLibParser
import fortress.modelfind._
import fortress.operations.TheoryOps._
import fortress.msfol._
import org.scalatest._

class CombinedModelTest extends UnitSuite {

    // Demonstrates SMTLib integer parsing and valid model counting on an example
    // squares_example.smt is a specification for the problem of finding square numbers in a given range
    // Here, we count the number of perfect squares between 100 and 5000
    test("squares example") {
        // println("Squares example: finds all perfect squares from 100 to 5000")
        val classLoader: ClassLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("squares_example.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)
        // println("Parsed theory from file:")
        // println(resultTheory)

        val finder = ModelFinder.createDefault()

        finder.setTheory(resultTheory)
        finder.checkSat() should be (ModelFinderResult.Sat)

        val model = finder.viewModel()

        val numModels = finder.countValidModels(resultTheory)
        // println("Found " + numModels + " models")

        // Found with WolframAlpha
        numModels should be (61)

        finder.setTheory(resultTheory)

        var result = finder.checkSat()
        while (result == ModelFinderResult.Sat) {
            // println("Found square: " + finder.viewModel().constantInterpretations(Var("soln").of(IntSort)).asInstanceOf[IntegerLiteral].value)
            result = finder.nextInterpretation()
        }
        // println("No more squares!")
    }

    // Demonstrates SMTLib integer parsing and valid model counting on an example
    // prime_example.smt is a specification for the problem of finding prime numbers in a given range
    // Here, we count the number of primes between 2 and 100
    test("prime example") {
        // println("Prime example: finds all primes from 2 to 100")
        val classLoader: ClassLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("prime_example.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)
        // println("Parsed theory from file:")
        // println(resultTheory)

        val finder = ModelFinder.createDefault()

        finder.setTheory(resultTheory)
        finder.checkSat() should be (ModelFinderResult.Sat)

        val model = finder.viewModel()

        val numModels = finder.countValidModels(resultTheory)
        // println("Found " + numModels + " models")

        // Found with WolframAlpha
        numModels should be (25)

        finder.setTheory(resultTheory)

        var result = finder.checkSat()
        while (result == ModelFinderResult.Sat) {
            // println("Found prime: " + finder.viewModel().constantInterpretations(Var("prime").of(IntSort)).asInstanceOf[IntegerLiteral].value)
            result = finder.nextInterpretation()
        }
        // println("No more primes!")
    }

    // Demonstrates SMTLib parsing, valid model counting, and model verification
    // Finds valid k-colourings for the complete graph on n vertices
    test("graph example") {
        val classLoader: ClassLoader = getClass.getClassLoader
        val file = new File(classLoader.getResource("graph_colouring.smt2").getFile)
        val fileStream = new FileInputStream(file)

        val parser = new SmtLibParser
        val resultTheory = parser.parse(fileStream)

        val finder = ModelFinder.createDefault()

        // K_n is n-colourable
        finder.setAnalysisScope(SortConst("vert"), 3)
        finder.setAnalysisScope(SortConst("colour"), 3)
        finder.setTheory(resultTheory)
        finder.checkSat() should be (ModelFinderResult.Sat)

        var model = finder.viewModel()
        resultTheory.verifyInterpretation(model)

        finder.countValidModels(resultTheory) should be (6)

        // K_n is not k-colourable for k < n
        finder.setTheory(resultTheory)
        finder.setAnalysisScope(SortConst("vert"), 8)
        finder.setAnalysisScope(SortConst("colour"), 7)
        finder.checkSat() should be (ModelFinderResult.Unsat)

        // K_n is k-colourable for k > n
        finder.setTheory(resultTheory)
        finder.setAnalysisScope(SortConst("vert"), 3)
        finder.setAnalysisScope(SortConst("colour"), 6)
        finder.checkSat() should be (ModelFinderResult.Sat)

        model = finder.viewModel()
        resultTheory.verifyInterpretation(model)

        finder.countValidModels(resultTheory) should be (120)
    }
}
