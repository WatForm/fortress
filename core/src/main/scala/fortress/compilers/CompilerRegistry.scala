package fortress.compilers

object CompilersRegistry {
    def fromString(str: String): Option[Compiler] = {
        str match {

            // StandardCompilers - use constants 
            case "Standard"  => Some(new StandardCompiler())
            case "StandardSI"  => Some(new StandardSICompiler())

            case "Claessen" => Some(new ClaessenCompiler())

            // use datatypes to make it finite
            case "DatatypeNoRangeEUF" => Some(new DatatypeNoRangeEUFCompiler())
            case "DatatypeWithRangeEUF" => Some(new DatatypeWithRangeEUFCompiler())
            case "DatatypeWithRangeNoEUF" => Some(new DatatypeWithRangeNoEUFCompiler())
            case "DatatypeNoRangeNoEUF" => Some(new DatatypeNoRangeNoEUFCompiler())

            // JoeSymmetryCompilers  
            case "v0"  => Some(new JoeONECompiler())
            case "v2"  => Some(new JoeTWOCompiler())
            case "v2si"  => Some(new JoeTWO_SICompiler())
            case "v3"  => Some(new JoeTHREECompiler())
            case "v3si"  => Some(new JoeTHREE_SICompiler())
            case "v4"  => Some(new JoeFOURCompiler())
            case "v4si"  => Some(new JoeFOUR_SICompiler())

            case _ => None
        }
    }

    def doesSortInference(str: String): Boolean = {
        str match {

            case "v2si" => true
            case "v3si" => true
            case "v4si" => true

            case _ => false

        }
    }
}   