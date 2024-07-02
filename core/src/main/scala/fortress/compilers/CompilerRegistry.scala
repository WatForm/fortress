package fortress.compilers

object CompilersRegistry {
    def fromString(str: String): Option[Compiler] = {
        str.toLowerCase() match {

            // StandardCompilers
            case "Standard"  => Some(new StandardCompiler())
            case "Claessen" => Some(new ClaessenCompiler())
            case "DatatypeNoRangeEUF" => Some(new DatatypeNoRangeEUFCompiler())
            case "DatatypeWithRange" => Some(new DatatypeWithRangeCompiler())
            case "DatatypeNoRange" => Some(new DatatypeNoRangeCompiler())

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
        str.toLowerCase() match {

            case "v2si" => true
            case "v3si" => true
            case "v4si" => true

            case _ => false

        }
    }
}   