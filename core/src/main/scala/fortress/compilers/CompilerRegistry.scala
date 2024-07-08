package fortress.compilers

import fortress.util.Errors

object CompilersRegistry {

    // this is the only place where string names are used
    // these MUST match the class name of the Compiler (minus the 'Compiler' on the end)

    def fromString(str: String): Option[Compiler] = {
        str match {

            // StandardCompilers - use constants 
            case "Standard"  => checkMatch(str,new StandardCompiler())
            case "StandardSI"  => checkMatch(str,new StandardSICompiler())

            case "Claessen" => checkMatch(str,new ClaessenCompiler())

            // use datatypes to make it finite
            case "DatatypeNoRangeEUF" => checkMatch(str,new DatatypeNoRangeEUFCompiler())
            case "DatatypeWithRangeEUF" => checkMatch(str,new DatatypeWithRangeEUFCompiler())
            case "DatatypeWithRangeNoEUF" => checkMatch(str,new DatatypeWithRangeNoEUFCompiler())
            case "DatatypeNoRangeNoEUF" => checkMatch(str,new DatatypeNoRangeNoEUFCompiler())

            // JoeSymmetryCompilers  
            case "JoeONE"  => checkMatch(str,new JoeONECompiler())
            case "JoeTWO"  => checkMatch(str,new JoeTWOCompiler())
            case "JoeTWO_SI"  => checkMatch(str,new JoeTWO_SICompiler())
            case "JoeTHREE"  => checkMatch(str,new JoeTHREECompiler())
            case "JoeTHREE_SI"  => checkMatch(str,new JoeTHREE_SICompiler())
            case "JoeFOUR"  => checkMatch(str,new JoeFOURCompiler())
            case "JoeFOUR_SI"  => checkMatch(str,new JoeFOUR_SICompiler())

            case _ => None
        }
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

    private def checkMatch(s:String, c:Compiler) = {
        Errors.Internal.assertion(c.name != s, s +"does not match"+ c.name)
        Some(c)        
    }

}   