package fortress.cli

import org.rogach.scallop._

import fortress.msfol._
import fortress.modelfind._
import fortress.inputs._
import fortress.compiler._
import fortress.util._
import fortress.logging._

import java.io._

class Conf(arguments: Seq[String]) extends ScallopConf(arguments) {
    val mode = opt[String](required = true)
    val scope = opt[Int](required = false)
    val version = opt[String](required = true)
    val file = trailArg[String](required = true)
    val scopeMap = props[Int]('S')
    val debug = opt[Boolean]()
    val timeout = opt[Int](required = true) // Timeout in seconds
    verify()
}

object FortressCli {
    def main(args: Array[String]): Unit = {
        val conf = new Conf(args)
        // println("file: " + conf.file())
        // println("version: " + conf.version())
        // println("scope: " + conf.scope())
        
        val parser = new SmtLibParser

        val theory = parser.parse(new FileInputStream(conf.file()))

        // Default scopes
        var scopes: Map[Sort, Int] = conf.scope.toOption match {
            case Some(scope) => {
                for(sort <- theory.sorts) yield (sort -> scope)
            }.toMap
            case None => Map()
        }

        // Override with specifc scopes
        for((sortName, scope) <- conf.scopeMap) {
            scopes += (Sort.mkSortConst(sortName) -> scope)
        }

        val integerSemantics = Unbounded

        conf.mode() match {
            case "count" => {
                val modelFinder = conf.version() match {
                    case "v0" => new FortressZERO
                    case "v1" => new FortressONE
                    case "v2" => new FortressTWO
                    case "v2si" => new FortressTWO_SI
                    case "v3" => new FortressTHREE
                    case "v3si" => new FortressTHREE_SI
                }

                modelFinder.setTheory(theory)
                for((sort, scope) <- scopes) {
                    modelFinder.setAnalysisScope(sort, scope)
                }
                modelFinder.setTimeout(Seconds(conf.timeout()))
                modelFinder.setBoundedIntegers(integerSemantics)

                val count = modelFinder.countValidModels(theory)
                println(count)
            }

            case "compile" => {
                val compiler = conf.version() match {
                    case "v0" => new FortressZEROCompiler(integerSemantics)
                    case "v1" => new FortressONECompiler(integerSemantics)
                    case "v2" => new FortressTWOCompiler(integerSemantics)
                    case "v2si" => new FortressTWOCompiler_SI(integerSemantics)
                    case "v3" => new FortressTHREECompiler(integerSemantics)
                    case "v3si" => new FortressTHREECompiler_SI(integerSemantics)
                }
                val loggers = if(conf.debug()) {
                    Seq(new StandardLogger(new PrintWriter(System.out)))
                } else Seq()
                val output = compiler.compile(theory, scopes, Seconds(conf.timeout()).toMilli, loggers)
                output match {
                    case Left(err) => println(err)
                    case Right(result) => println(result.theory)
                }
            }

            case "decision" => {
                val modelFinder = conf.version() match {
                    case "v0" => new FortressZERO
                    case "v1" => new FortressONE
                    case "v2" => new FortressTWO
                    case "v2si" => new FortressTWO_SI
                    case "v3" => new FortressTHREE
                    case "v3si" => new FortressTHREE_SI
                }

                val loggers = if(conf.debug()) {
                    Seq(new StandardLogger(new PrintWriter(System.out)))
                } else Seq()
                for(logger <- loggers) {
                    modelFinder.addLogger(logger)
                }

                modelFinder.setTheory(theory)
                for((sort, scope) <- scopes) {
                    modelFinder.setAnalysisScope(sort, scope)
                }
                modelFinder.setTimeout(Seconds(conf.timeout()))
                modelFinder.setBoundedIntegers(integerSemantics)

                val result = modelFinder.checkSat()
                println(result)
            }
            case other => {
                System.err.println("Invalid mode: " + other)
                System.exit(1)
            }
        } 
    }
}