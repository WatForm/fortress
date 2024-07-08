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
            case "JoeZERO" => checkMatch(str, new JoeZEROModelFinder())
            case "JoeOnee" => checkMatch(str, new JoeONEModelFinder())
            case "JoeTWO" => checkMatch(str, new JoeTWOModelFinder())
            case "JoeTWO_SI" => checkMatch(str, new JoeTWO_SIModelFinder())
            case "JoeTHREE" => checkMatch(str, new JoeTHREEModelFinder())
            case "JoeTHREE_SI" => checkMatch(str, new JoeTHREE_SIModelFinder())
            case "JoeFOUR" => checkMatch(str, new JoeFOURModelFinder())
            case "JoeFOUR_SI" => checkMatch(str, new JoeFOUR_SIModelFinder())
                
            case _ => None
        }
    }

    private def checkMatch(s:String, mf:ModelFinder) = {
        Errors.Internal.assertion(mf.name != s, s +"does not match"+ mf.name)
        Some(mf)        
    }

}