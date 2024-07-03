package fortress.modelfinders

// this registry matches string names to model finders beyond the default one

object ModelFindersRegistry {
    def fromString(str: String): Option[ModelFinder] = {
        str.toLowerCase() match {

            // Standard Model Finders
            case "standard" => Some(new StandardModelFinder())

            // Joe's Model Finders
            case "zero" | "fortresszero" => Some(new JoeZEROModelFinder())
            case "one" | "fortressone" => Some(new JoeONEModelFinder())
            case "two" | "fortresstwo" => Some(new JoeTWOModelFinder())
            case "two_si" | "fortresstwo_si" => Some(new JoeTWO_SIModelFinder())
            case "three" | "fortressthree" => Some(new JoeTHREEModelFinder())
            case "three_si" | "fortressthree_si" => Some(new JoeTHREE_SIModelFinder())
            case "four" | "fortressfour" => Some(new JoeFOURModelFinder())
            case "four_si" | "fortressfour_si" => Some(new JoeFOUR_SIModelFinder())
                
            case _ => None
        }
    }
}