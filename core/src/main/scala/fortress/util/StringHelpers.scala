package fortress.util

object StringHelpers {
    // return the string name without ModelFinder on the end of it
	def chopOff(s:String, endChop:String) =  
    	s.substring(0,s.indexOf(endChop))
}