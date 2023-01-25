package fortress.problemstate

import fortress.util.Errors

sealed trait Scope {
    def isExact: Boolean // If false solution can use up to size elements
    def size: Int
    def isUnchanging: Boolean // For dumping only (currently) the problem cannot be attempted at different scope sizes
}

case class ExactScope(size: Int, isUnchanging: Boolean) extends Scope {
    Errors.Internal.precondition(size > 0, "ExactScope size must be positive")
    def isExact = true
}
object ExactScope{
    def apply(size: Int) = new ExactScope(size, false)
    def apply(size: Int, fixed: Boolean) = new ExactScope(size, fixed)
}

case class NonExactScope(size: Int, isUnchanging: Boolean) extends Scope {
    Errors.Internal.precondition(size > 0, "NonExactScope size must be positive")
    def isExact = false
}
object NonExactScope{
    def apply(size: Int) = new NonExactScope(size, false)
    def apply(size: Int, fixed: Boolean) = new NonExactScope(size, fixed)
}