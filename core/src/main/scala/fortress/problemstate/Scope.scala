package fortress.problemstate

import fortress.util.Errors

sealed trait Scope {
    def isExact: Boolean
    def size: Int
}

case class ExactScope(size: Int) extends Scope {
    Errors.Internal.precondition(size > 0, "ExactScope size must be positive")
    def isExact = true
}

case class NonExactScope(size: Int) extends Scope {
    Errors.Internal.precondition(size > 0, "NonExactScope size must be positive")
    def isExact = false
}