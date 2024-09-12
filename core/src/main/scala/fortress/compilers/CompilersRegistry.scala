package fortress.compilers

import fortress.util.Errors
import fortress.problemstate._
import fortress.transformers._
import scala.collection.mutable.ListBuffer

object CompilersRegistry {

    // this is the only place where string names are used
    // these MUST match the class name of the Compiler (minus the 'Compiler' on the end)

    def fromString(str: String): Compiler = {

        // it's a little awkward to wrap every return entry
        // in checkName, but otherwise we have to wrap the return entry
        // in Some and deal with the option type in checkName
        val c:Compiler = str match {

            // StandardCompilers - use constants 
            case "Standard"  => new StandardCompiler()
            case "StandardSI"  => new StandardSICompiler()

            case "MaxUnboundedScopes" => new MaxUnboundedScopesCompiler()

            case "Evaluate" => new EvaluateCompiler()
            case "DatatypeNoRangeEUFEvaluate" => new DatatypeNoRangeEUFEvaluateCompiler()
            case "DatatypeWithRangeEUFEvaluate" => new DatatypeWithRangeEUFEvaluateCompiler()

            // Bitvector
            case "UncheckedBV" => new UncheckedBVCompiler()
            case "NOBV" => new NOBVCompiler()

            case "Eijck" => new EijckCompiler()

            case "AlmostNothing" => new AlmostNothingCompiler()

            // use datatypes to make it finite
            case "DatatypeNoRangeEUF" => new DatatypeNoRangeEUFCompiler()
            case "DatatypeWithRangeEUF" => new DatatypeWithRangeEUFCompiler()
            case "DatatypeWithRangeNoEUF" => new DatatypeWithRangeNoEUFCompiler()
            case "DatatypeNoRangeNoEUF" => new DatatypeNoRangeNoEUFCompiler()

            // JoeSymmetryCompilers  
            case "JoeONE"  => new JoeONECompiler()
            case "JoeTWO"  => new JoeTWOCompiler()
            case "JoeTWO_SI"  => new JoeTWO_SICompiler()
            case "JoeTHREE"  => new JoeTHREECompiler()
            case "JoeTHREE_SI"  => new JoeTHREE_SICompiler()
            case "JoeFOUR"  => new JoeFOURCompiler()
            case "JoeFOUR_SI"  => new JoeFOUR_SICompiler()

            case _ => {
                throw Errors.API.compilerDoesNotExist(str)
                null
            }
        }
        checkName(str,c)
    }

    def doesSortInference(str: String): Boolean = {
        str match {
            case "StandardSI" => true
            case "JoeTWO_SI" => true
            case "JoeTHREE_SI" => true
            case "JoeFOUR_SI" => true

            case _ => false

        }
    }

    private def checkName(s:String, c:Compiler): Compiler = {
        Errors.Internal.assertion(c.name ==s, s +" does not match "+ c.name)
        c        
    }


    def NullTransformerList:ListBuffer[ProblemStateTransformer] = {
        val ts = new scala.collection.mutable.ListBuffer[ProblemStateTransformer]
        ts
    }

    def ListOfOne(x:ProblemStateTransformer):ListBuffer[ProblemStateTransformer] = {
        val ts = NullTransformerList
        ts += x
        ts
    }
}   