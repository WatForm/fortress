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
    val scope = opt[Int](required = false)
    val file = trailArg[String](required = true)
    val scopeMap = props[Int]('S')
    val timeout = opt[Int](required = true) // Timeout in seconds
    val generate = opt[Boolean]() // Whether to generate a model
    verify()
}

object FortressCli {
    def main(args: Array[String]): Unit = {
        val conf = new Conf(args)
        
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

        val modelFinder = new FortressTHREE_SI

        modelFinder.setTheory(theory)
        for((sort, scope) <- scopes) {
            modelFinder.setAnalysisScope(sort, scope)
        }
        modelFinder.setTimeout(Seconds(conf.timeout()))
        modelFinder.setBoundedIntegers(integerSemantics)

        val result = modelFinder.checkSat()
        println(result)
        if(conf.generate()) {
            result match {
                case SatResult => println(modelFinder.viewModel())
            }
        }
    }
}