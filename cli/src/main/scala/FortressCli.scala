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
import fortress.operations.InterpretationVerifier
import fortress.interpretation.Interpretation

class Conf(arguments: Seq[String]) extends ScallopConf(arguments) {

    // these options all have to be lower case

    val scope = opt[Int](required = false, descr="default scope for sorts")
    // Scope Map could be props[Scope] with a special converter, but we already change the keys so its not a huge deal
    // NAD?  how are duplicates in the specification of the scope at the CLI handled here?
    // as in fortress -SA=2 B?=3 A=4u ?? it's a map so currently no error message is given
    val scopeMap = props[String]('S', descr="scope sizes for individual sorts (overrides those in file) in the form <sort>[?]=<scope>[u] ex: A=2 B?=3 C=4u ... where ? = non-exact and u = unchanging.")
    val file = trailArg[String](required = true, descr="file(s) to run on")

    val debug = opt[Boolean](descr="Writes debug output to console", noshort=true)
    val verbose = opt[Boolean](descr="Writes steps in process to console", noshort=true)
    
    val timeout = opt[Int](required = true, descr="(required) timeout in seconds") // Timeout in seconds

    // 2024-07-15 NAD changed these from being ModelFinders to just Strings and do the conversion 
    // from a String to a ModelFinder below in main() to make it easier to handle exception
    // that comes from not finding it in the lookup registry
    val modelfinder = opt[String](required = false, descr="modelfinder to use (default StandardCompiler/Z3NonIncSolver)")

    val solver = opt[String](required = false, descr="solver to use (default Z3NonIncSolver)")

    val compiler = opt[String](required = false, descr="compiler to use (default StandardCompiler)")

    val transformers = opt[List[String]](required = false,short='T', descr="specify transformers in order")

    val compileOnly = opt[Boolean](descr="Output the SMT-LIB after the compile and stop",noshort=true)

    mutuallyExclusive(modelfinder, transformers)
    mutuallyExclusive(modelfinder, compiler)
    mutuallyExclusive(modelfinder, solver)
    mutuallyExclusive(compiler, transformers)

    val generate = opt[Boolean](descr="generate and print a model if a SAT result")
    val verifyInterpretation = opt[Boolean](short='V', descr="Verify a model if a SAT result")
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

        // Default scopes from cmd line; might be none
        // assumes duplicates in the file mapping having already been dealt
        // with in the parse
        var scopes: Map[Sort, Scope] = conf.scope.toOption match {
            case Some(scope) => {
                if (scope <= 0) Errors.cliError("default scope must be above zero")
                for(sort <- theory.sorts) yield sort -> ExactScope(scope)
            }.toMap
            case None => Map()
        }
        // Scopes in file -- could be none; override defaults
        for ((sort,scope) <- parser.getScopes().asScala) scopes += (sort -> scope)

        // Scopes from cmd line, override defaults and scopes in file
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

            // built in sorts
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
            try {
                conf.modelfinder.toOption match {
                    case Some(mfname) => ModelFindersRegistry.fromString(mfname)
                    case None => new StandardModelFinder() // the default one
                }
            } catch {
                case (Errors.API.modelFinderDoesNotExist(y)) =>
                    // will exit gracefully
                    Errors.cliError("Model finder does not exist: "+y) 
                new StandardModelFinder() // will never reach here               
            }

        // mutually exclusive with the specification of a model finder
        if (conf.compiler.isSupplied) {
            try {
                conf.compiler.toOption match {
                    case Some(compiler) => modelFinder.setCompiler(CompilersRegistry.fromString(compiler))
                    case None => () // leave as StandardCompiler in model finder
                }
            } catch {
                case (Errors.API.compilerDoesNotExist(y)) => 
                    // will exit gracefully
                    Errors.cliError("Compiler does not exist: "+y)
            }                
        }

        // mutually exclusive with the specification of a model finder
        if (conf.transformers.isSupplied) {
            try {
                val tlist = CompilersRegistry.NullTransformerList
                for (t <- conf.transformers.toOption.get ) {
                    tlist += TransformersRegistry.fromString(t)
                }
                modelFinder.setCompiler(new ConfigurableCompiler(tlist.toList))
            } catch {
                case (Errors.API.transformerDoesNotExist(y)) => 
                    // will exit gracefully
                    Errors.cliError("Transformer does not exist: "+y)
            }                                            
        }

        // mutually exclusive with the specification of a model finder
        if (conf.solver.isSupplied) {
            try {
                conf.solver.toOption match {
                    case Some(solver) => modelFinder.setSolver(SolversRegistry.fromString(solver))
                    case None => () // leave as default Solver in model finder
                }
            } catch {
                case (Errors.API.solverDoesNotExist(y)) => 
                    // will exit gracefully
                    Errors.cliError("Solver does not exist: "+y)
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

        if (conf.verbose()) println("Setting scopes (if any) ...")
        for((sort, scope) <- scopes) {
            modelFinder.setScope(sort, scope)
        }
        modelFinder.setTimeout(Seconds(conf.timeout()))

        if (conf.verbose()) println("Compiling ...")

        modelFinder.compile() match {
            case Left(ce) => { 
                Errors.cliError("Error compiling" + ce.toString())
            }
            case Right(cr) => {
                if (conf.compileOnly()) {
                    val theoryAfterCompile = cr.theory

                    //println("=====original=====")
                    // This may have DEs in it !  We parse the input constants
                    // as DEs if they have certain names (and ignore their constant decl
                    // if they have those names)
                    // If we wanted to directly dump the input then we would
                    // need to convert the DEs back to constants 
                    //println(TheoryOps.wrapTheory(TypecheckSanitizeTransformer(ProblemState(theory, scopes)).theory).smtlib)
                    //println("========new=======")
                    println(TheoryOps.wrapTheory(theoryAfterCompile).smtlib)
                    //println("==================")
                    System.exit(1)
                }
            }
        }
        if (conf.verbose()) println("Solving ...")
        // this won't redo compiling due to flags in the modelFinder
        val result = modelFinder.checkSat()
        println(result)

        if (result == SatResult){
            if (conf.generate() || conf.verifyInterpretation()){
                val model: Interpretation = modelFinder.viewModel()
                if (conf.generate()){
                    println("-----model-----")
                    println(model)
                    println("---end model---")
                }
                if (conf.verifyInterpretation()){
                    val verifier: InterpretationVerifier = new InterpretationVerifier(theory) // Takes the original theory
                    val verifyResult = verifier.verifyInterpretation(model)
                    if (verifyResult){
                        println("Valid Interpretation")
                    } else {
                        println("Invalid Interpretation")
                    }
                }
            }
        }

        if(conf.generate()) {
            result match {
                case SatResult => println(modelFinder.viewModel())
                case _ => { }
            }
        }
    }
}