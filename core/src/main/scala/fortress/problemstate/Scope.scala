package fortress.problemstate

import fortress.util.Errors

abstract class Scope {
    var isExact: Boolean // If false scope can have up to size elements
    var size: Int
    var isFixed: Boolean // the problem cannot be attempted at different scope sizes

    // initialization
    Errors.Internal.precondition(size > 0, "Scope size must be positive")

    def mkFixed():Unit = {
         isFixed = true
    }
}

// these are never used with a match statement so let's not make them 
// case classes and let them be mutable
class ExactScope(size: Int, isFixed: Boolean = false) extends Scope {
    var isExact = true
}

class NonExactScope(size: Int, isFixed: Boolean = false) extends Scope {
    var isExact = false
}

