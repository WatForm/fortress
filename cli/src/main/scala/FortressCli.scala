package fortress.cli

import org.rogach.scallop._

import fortress.msfol._
import fortress.modelfind._
import fortress.inputs._
import fortress.compiler._
import fortress.util._
import fortress.logging._
import fortress.transformers._

import java.io._
import java.{util => ju}

class Conf(arguments: Seq[String]) extends ScallopConf(arguments) {
    val scope = opt[Int](required = false)
    val file = trailArg[String](required = true)
    val scopeMap = props[Int]('S')
    val timeout = opt[Int](required = true) // Timeout in seconds

    // modelfinder.
    val mfConverter = singleArgConverter[ModelFinder](FortressModelFinders.fromString(_).get, {
        case x: ju.NoSuchElementException  => Left("Not a valid FortressModelFinder")
    })
    val modelFinder = opt[ModelFinder](required =  false)(mfConverter)

    // transformers if manually specifying
    val transfromerConverter = new ValueConverter[List[ProblemStateTransformer]]{
        def parse(s: List[(String, List[String])]): Either[String,Option[List[ProblemStateTransformer]]] = {
            // Don't really care if someone makes separate lists of transformers, so we fold them together
            val transformerNames = s.map(_._2).flatten 
            try {
                Right(Some(transformerNames.map(Transformers.fromString(_))))
            } catch {
                case e: Errors.API.DoesNotExistError => Left(e.getMessage())
            }
        }
        val argType: ArgType.V = ArgType.LIST
    }
    val transformers = trailArg[List[ProblemStateTransformer]](required=true)(transfromerConverter)

    mutuallyExclusive(modelFinder, transformers)

    val generate = opt[Boolean]() // Whether to generate a model
    verify()
}

object FortressCli {
    def main(args: Array[String]): Unit = {
        val conf = new Conf(args)
        
        val parser : TheoryParser = new SmtLibParser
        val parseResult = parser.parse(new FileInputStream(conf.file()))
        val theory : Theory = parseResult match {
            case Left(x) =>
                System.err.println("Parse error: " + x.getMessage);
                System.exit(1)
                null
            case Right(x) => x
        }

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

        val modelFinder: ModelFinder = conf.modelFinder.toOption match {
            case Some(mf) => mf
            case None => conf.transformers.toOption match {
                case Some(transformers) => new SimpleModelFinder(transformers.toSeq)
                // Default to THREE_SI
                case None => new FortressTHREE_SI
            }
        }

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
                case _ => { }
            }
        }
    }
}