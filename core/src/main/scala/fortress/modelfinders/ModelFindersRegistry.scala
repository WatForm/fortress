package fortress.modelfinders

import fortress.util.Errors

// this registry matches string names to model finders beyond the default one

object ModelFindersRegistry {

    // this is the only place where string names are used
    // these MUST match the class name of the ModelFinder (minus the 'ModelFinder' on the end)
    def fromString(str: String): ModelFinder = {
        val mf:ModelFinder = str match {

            // Standard Model Finders
            case "Standard" =>  new StandardModelFinder()

            // Joe's Model Finders
            case "JoeZERO" =>  new JoeZEROModelFinder()
            case "JoeOnee" =>  new JoeONEModelFinder()
            case "JoeTWO" =>  new JoeTWOModelFinder()
            case "JoeTWO_SI" =>  new JoeTWO_SIModelFinder()
            case "JoeTHREE" =>  new JoeTHREEModelFinder()
            case "JoeTHREE_SI" =>  new JoeTHREE_SIModelFinder()
            case "JoeFOUR" =>  new JoeFOURModelFinder()
            case "JoeFOUR_SI" =>  new JoeFOUR_SIModelFinder()
                
            case _ => {
                throw Errors.API.modelFinderDoesNotExist(str)
                null
            }
        }
        checkName(str,mf)
    }

    private def checkName(s:String, mf:ModelFinder): ModelFinder = {
        Errors.Internal.assertion(mf.name == s, s +" does not match "+ mf.name)
        mf        
    }

}