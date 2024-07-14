package fortress.cli

import org.rogach.scallop._
import fortress.msfol._
import fortress.modelfinders._
import fortress.inputs._
import fortress.compilers._
import fortress.solvers._
import fortress.util._
import fortress.logging._
import fortress.problemstate._
import fortress.transformers._

import scala.collection.JavaConverters._
import java.io._
import java.{util => ju}
import fortress.operations.TheoryOps

class Conf(arguments: Seq[String]) extends ScallopConf(arguments) {
    val scope = opt[Int](required = false, descr="default scope for all sorts")
    // Scope Map could be props[Scope] with a special converter, but we already change the keys so its not a huge deal
    val scopeMap = props[String]('S', descr="scope sizes for individual sorts in the form <sort>[?]=<scope>[u] ex: A=2 B?=3 C=4u ... where ? = non-exact and u = unchanging.")
    val file = trailArg[String](required = true, descr="file(s) to run on")

    // TODO: we want to flip the meaning of this and change its name
    val importScope = opt[Boolean](descr="Import scope from smttc file if present.")

    val debug = opt[Boolean](descr="Writes debug output to console", noshort=true)
    val verbose = opt[Boolean](descr="Writes even more output to console", noshort=true)
    
    val timeout = opt[Int](required = true, descr="timeout in seconds") // Timeout in seconds

    // model finder.
    val mfConverter = singleArgConverter[ModelFinder](ModelFindersRegistry.fromString(_), {
        case x: ju.NoSuchElementException  => Left("Not a valid ModelFinder")
    })
    val modelFinder = opt[ModelFinder](required = false, descr="modelfinder to use (default StandardCompiler/Z3NonIncSolver)")(mfConverter)

    // solver
    val solverConverter = singleArgConverter[Solver](SolversRegistry.fromString(_), {
        case x: ju.NoSuchElementException  => Left("Not a valid Solver")
    })
    val solver = opt[Solver](required = false, descr="solver to use (default Z3NonIncSolver)")(solverConverter)

    // compiler
    val compilerConverter = singleArgConverter[Compiler](CompilersRegistry.fromString(_), {
        case x: ju.NoSuchElementException  => Left("Not a valid Compiler")
    })
    val compiler = opt[Compiler](required = false, descr="compiler to use (default StandardCompiler)")(compilerConverter)

    // transformers if manually specifying
    val transformerConverter = new ValueConverter[List[ProblemStateTransformer]]{
        def parse(s: List[(String, List[String])]): Either[String,Option[List[ProblemStateTransformer]]] = {
            // Don't really care if someone makes separate lists of transformers, so we fold them together
            val transformerNames = s.map(_._2).flatten 
            try {
                // Handle the empty list properly
                if (transformerNames.isEmpty){
                    Right(None)
                } else {
                    Right(Some(transformerNames.map(TransformersRegistry.fromString(_))))
                }
            } catch {
                case e: Errors.API.transformerDoesNotExist => Left(e.getMessage())
            }
        }
        val argType: ArgType.V = ArgType.LIST
    }
    val transformers = opt[List[ProblemStateTransformer]](required = false,short='T', descr="alternative to modelfinder. specify transformers in order")(transformerConverter)

    mutuallyExclusive(modelFinder, transformers)
    mutuallyExclusive(modelFinder, compiler)
    mutuallyExclusive(modelFinder, solver)
    mutuallyExclusive(compiler, transformers)

    val generate = opt[Boolean](descr="generate a model if a SAT result") 
    verify()
}

object FortressCli {
    def main(args: Array[String]): Unit = {
        val conf = new Conf(args)

        if (conf.debug()){
            println("======conf======")
            println(conf.summary)
            println("----------------")
        }
       
        if (conf.verbose()) println("Parsing ...") 
        val parser : SmtLibParser = new SmtLibParser
        val parseResult = parser.parse(conf.file()) 
        val theory : Theory = parseResult match {
            case Left(x) =>
                System.err.println("Parse error: " + x.getMessage);
                System.exit(1)
                null
            case Right(x) => x
        }

        // Scopes from cmd line
        if (conf.verbose()) println("Setting scopes (if any)")
        var scopes: Map[Sort, Scope] = conf.scope.toOption match {
            case Some(scope) => {
                for(sort <- theory.sorts) yield sort -> ExactScope(scope)
            }.toMap
            case None => Map()
        }
        // Scopes in file
        if (conf.importScope()){
            val parsedScopes = parser.getScopes().asScala
            scopes = scopes ++ parsedScopes
        }

        // NAD? what stops the scope of a sort from being specified multiple
        // times at the cmd line and/or in the file??
        // Override with specific scopes
        for ( (sort, scope) <- conf.scopeMap ) {
            var scopeValue: Int = 0
            var isUnchanging = false
            if (scope.charAt(scope.length-1) == 'u'){
                scopeValue = scope.substring(0, scope.length - 1).toInt
                isUnchanging = true
            } else {
                scopeValue = scope.toInt
                isUnchanging = false
            }
            if (scopeValue <= 0) {
                System.err.println("Scope must be > 0. Got " + scopeValue.toString()+".");
                System.exit(1)
            }
            
            var sortName = sort
            val scopeVal = if( sort.charAt(sort.length-1) == '?' ) { // "P?=2"
                // NonExact Scope
                sortName =  sort.substring(0, sort.length-1)
                NonExactScope(scopeValue, isUnchanging)
            }
            else {  // "P=2"
                // Exact Scope
                ExactScope(scopeValue, isUnchanging)
            }

            val sortConst = sortName.toLowerCase match {
                case "int" | "intsort" => IntSort
                case _ => SortConst(sortName)
            }
            scopes += (sortConst -> scopeVal)
        }

        if(conf.debug()){
            println("Scopes:")
            println(scopes)
        }

        val modelFinder: ModelFinder = 
            conf.modelFinder.toOption match {
                case Some(mf) => mf
                case None => new StandardModelFinder() // the default one
            }

        // mutually exclusive with the specification of a model finder
        if (conf.compiler.isSupplied) {
            conf.compiler.toOption match {
                case Some(compiler) => modelFinder.setCompiler(compiler)
                case None => Errors.Internal.impossibleState
            }
        }

        // mutually exclusive with the specification of a model finder
        if (conf.transformers.isSupplied) {
            modelFinder.setCompiler(new ConfigurableCompiler(conf.transformers.apply()))
        }

        // mutually exclusive with the specification of a model finder
        if (conf.solver.isSupplied) {
            conf.solver.toOption match {
                case Some(solver) => modelFinder.setSolver(solver)
                case None => Errors.Internal.impossibleState
            }
        }


        val loggers = if(conf.debug()) {
            Seq(new StandardLogger(new PrintWriter(System.out)))
        } else Seq()

        for (logger <- loggers){
            modelFinder.addLogger(logger)
        }

        if (conf.verbose()) println("Setting theory ...")
        modelFinder.setTheory(theory)
        println("Setting scopes (if any) ...")
        for((sort, scope) <- scopes) {
            modelFinder.setScope(sort, scope)
        }
        modelFinder.setTimeout(Seconds(conf.timeout()))

        // NAD? this seems to run the compiler separately from the model finder??? 
        if(conf.debug() && conf.verbose() && conf.transformers.isSupplied){
            val compiler = new ConfigurableCompiler(conf.transformers.apply())
            if (conf.verbose()) println("Compiling ...")
            val result = compiler.compile(
                theory, scopes,
                Seconds(conf.timeout()).toMilli, Seq.empty,
                verbose = conf.verbose()
            ).fold(
                ce => println("Error compiling", ce),
                cr => {
                    val result = cr.theory
                    println("=====original=====")
                    println(TheoryOps.wrapTheory(TypecheckSanitizeTransformer(ProblemState(theory, scopes)).theory).smtlib)
                    println("========new=======")
                    println(TheoryOps.wrapTheory(cr.theory).smtlib)
                    println("==================")
                }
            )
        }
        if (conf.verbose()) println("Solving ...")
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