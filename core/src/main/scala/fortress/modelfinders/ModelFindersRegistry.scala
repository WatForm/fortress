package fortress.modelfinders

import fortress.util.Errors

// this registry matches string names to model finders beyond the default one

object ModelFindersRegistry {

    // this is the only place where string names are used
    // these MUST match the class name of the ModelFinder (minus the 'ModelFinder' on the end)
    def fromString(str: String): Option[ModelFinder] = {
        str match {

            // Standard Model Finders
            case "Standard" => checkMatch(str, new StandardModelFinder())

            // Joe's Model Finders
            case "JoeZERO" => Some(new JoeZEROModelFinder())
            case "JoeOnee" => Some(new JoeONEModelFinder())
            case "JoeTWO" => Some(new JoeTWOModelFinder())
            case "JoeTWO_SI" => Some(new JoeTWO_SIModelFinder())
            case "JoeTHREE" => Some(new JoeTHREEModelFinder())
            case "JoeTHREE_SI" => Some(new JoeTHREE_SIModelFinder())
            case "JoeFOUR" => Some(new JoeFOURModelFinder())
            case "JoeFOUR_SI" => Some(new JoeFOUR_SIModelFinder())
                
            case _ => None
        }
    }

    private def checkMatch(s:String, mf:ModelFinder) = {
        Errors.Internal.assertion(mf.name != s, s +"does not match"+ mf.name)
        Some(mf)        
    }

}