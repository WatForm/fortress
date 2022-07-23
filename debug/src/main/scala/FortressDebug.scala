package fortress.cli

import org.rogach.scallop._

import fortress.msfol._
import fortress.modelfind._
import fortress.inputs._
import fortress.compiler._
import fortress.util._
import fortress.logging._
import fortress.operations.TheoryOps._
import fortress.transformers._

import java.io._

class Conf(arguments: Seq[String]) extends ScallopConf(arguments) {
    val mode = opt[String](required = true)
    val scope = opt[Int](required = true) // scope is required for compile/decision/count
    val version = opt[String](required = true)
    val file = trailArg[String](required = true)
    val scopeMap = props[Int]('S')
    val debug = opt[Boolean]()
    val rawdata = opt[Boolean]()
    val timeout = opt[Int](required = true) // Timeout in seconds
    val validate = opt[Boolean]() // verify returned instance for SAT problems
    val viewModel = opt[Boolean]()
    verify()
}

object FortressDebug {
    def main(args: Array[String]): Unit = {
        val conf = new Conf(args)

        val parser: TheoryParser = {
            val extension = conf.file().split('.').last
            extension match {
                case "p" => new TptpFofParser
                case "smt2" => new SmtLibParser
                case _ => {
                    System.err.println("Invalid file extension: " + extension)
                    System.exit(1)
                    null
                }
            }
        }
        val result = parser.parse(conf.file())
        val theory : Theory = result match {
            case Left(x) =>
                System.err.println("Parse error: " + x.getMessage);
                System.exit(1)
                null
            case Right(x) => x
        }

        // Default scopes
        var scopes: Map[Sort, (Int, Boolean)] = conf.scope.toOption match {
            case Some(scope) => {
                for(sort <- theory.sorts) yield (sort -> (scope, true))
            }.toMap
            case None => Map()
        }

        // Override with specific scopes
        for((sortName, scope) <- conf.scopeMap) {
            scopes += (Sort.mkSortConst(sortName) -> scope)
        }

        // val integerSemantics = Unbounded

        var loggers = if (conf.debug()) {
            Seq(new StandardLogger(new PrintWriter(System.out)))
        } else if (conf.rawdata()) {
            Seq(new RawDataLogger(new PrintWriter(System.out)))
        } else Seq()

        conf.mode() match {
            case "decision" => {
                val modelFinder = conf.version() match {
                    case "v0" => new FortressZERO
                    case "v1" => new FortressONE
                    case "v2" => new FortressTWO
                    case "v2si" => new FortressTWO_SI
                    case "v3" => new FortressTHREE
                    case "v3si" => new FortressTHREE_SI
                    case "v4" => new FortressFOUR
                    case "v4si" => new FortressFOUR_SI
//                    case "upperIter" => new IterativeUpperBoundModelFinder
//                    case "parIter" => new ParallelIterativeUpperBoundModelFinder
                    case "upperND" => new NonDistUpperBoundModelFinder
                    case "upperPred" => new PredUpperBoundModelFinder
                }

                for(logger <- loggers) {
                    modelFinder.addLogger(logger)
                }

                modelFinder.setTheory(theory)
                for((sort, scope) <- scopes) {
                    modelFinder.setAnalysisScope(sort, scope._1, scope._2)
                }
                modelFinder.setTimeout(Seconds(conf.timeout()))
                //modelFinder.setBoundedIntegers(integerSemantics)

                val result = modelFinder.checkSat()
                println(result)
                if (conf.validate() && result.equals(SatResult)) {
                    println("Verifying returned instance: " + theory.verifyInterpretation(modelFinder.viewModel()))
                }
                if (conf.viewModel() && result.equals(SatResult)) {
                    println(modelFinder.viewModel())
                }
            }

            case "count" => {
                val modelFinder = conf.version() match {
                    case "v0" => new FortressZERO
                    case "v1" => new FortressONE
                    case "v2" => new FortressTWO
                    case "v2si" => new FortressTWO_SI
                    case "v3" => new FortressTHREE
                    case "v3si" => new FortressTHREE_SI
                    case "unbounded" => new FortressUnbounded
                    case "v3sill" => new FortressLearnedLiterals
                }

                modelFinder.setTheory(theory)
                for((sort, scope) <- scopes) {
                    modelFinder.setAnalysisScope(sort, scope._1, scope._2)
                }
                modelFinder.setTimeout(Seconds(conf.timeout()))
                //modelFinder.setBoundedIntegers(integerSemantics)

                val count = modelFinder.countValidModels(theory)
                println(count)
            }

            case "compile" => {
                val compiler = conf.version() match {
                    case "v0" => new FortressZEROCompiler()
                    case "v1" => new FortressONECompiler()
                    case "v2" => new FortressTWOCompiler()
                    case "v2si" => new FortressTWOCompiler_SI()
                    case "v3" => new FortressTHREECompiler()
                    case "v3si" => new FortressTHREECompiler_SI()
                }
                val output = compiler.compile(theory, scopes, Seconds(conf.timeout()).toMilli, loggers)
                output match {
                    case Left(err) => println(err)
                    case Right(result) => println(result.theory)
                }
            }

            case "checkfornewsorts" => {
                val compiler = conf.version() match {
                    case "v2si" => new FortressTWOCompiler_SI()
                    case "v3si" => new FortressTHREECompiler_SI()
                    case other => {
                        System.err.println("Invalid model finder for looking for new sorts "+ other )
                        System.exit(1)
                    }
                }
                val old_num_sorts = wrapTheory(theory).sortCount

                // the following is enough to determine if there are new sorts
                // TypecheckSanitizeTransformer: Theory -> Theory
                val theory2 = TypecheckSanitizeTransformer.apply(theory)
                // wrapTheory is for operations on theories
                val new_sorts_present = wrapTheory(theory2).newSortsInferred
                if (new_sorts_present) {
                    var analysisScopes: Map[Sort, (Int, Boolean)] = Map.empty
                    for((sort, scope) <- scopes) {
                        analysisScopes = analysisScopes + (sort -> scope)
                    }
                    val ps2 = ProblemState.apply(theory2,analysisScopes)
                    // next EnumEliminationTransformer:ProblemState -> ProblemState 
                    val ps3 = EnumEliminationTransformer.apply(ps2)
                    // doing SortInference is necessary to actually count the new sorts 
                    //    and EnumElimination is done before SortInference
                    // SortInferenceTransformer: ProblemState -> ProblemState
                    val theory4 = SortInferenceTransformer(ps3).theory
                    val new_num_sorts = wrapTheory(theory4).sortCount
                    println("New sorts inferred, original number= " + old_num_sorts.toString +" new number= " + new_num_sorts.toString)
                } else {
                    println("No new sorts inferred")
                }
            }
            case other => {
                System.err.println("Invalid mode: " + other)
                System.exit(1)
            }
        }
    }
}