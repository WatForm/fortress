package fortress.problemstate

import fortress.util.Errors

sealed trait Scope {
    def isExact: Boolean // If false scope can have up to size elements
    def size: Int
    def isUnchanging: Boolean // the problem cannot be attempted at different scope sizes
    def mkUnchanging(): Scope

    // moving towards giving it a new name
    def isFixed():Boolean = isUnchanging
}

case class ExactScope(size: Int, isUnchanging: Boolean) extends Scope {
    Errors.Internal.precondition(size > 0, "ExactScope size must be positive")
    def isExact = true
    def mkUnchanging(): ExactScope =
        new ExactScope(this.size, true)

}
object ExactScope{
    def apply(size: Int) = new ExactScope(size, false)
    def apply(size: Int, isUnchanging: Boolean) = new ExactScope(size, isUnchanging)
}

case class NonExactScope(size: Int, isUnchanging: Boolean) extends Scope {
    Errors.Internal.precondition(size > 0, "NonExactScope size must be positive")
    def isExact = false

    def mkUnchanging(): NonExactScope =
        new NonExactScope(this.size, true)
}
object NonExactScope{
    def apply(size: Int) = new NonExactScope(size, false)
    def apply(size: Int, isUnchanging: Boolean) = new NonExactScope(size, isUnchanging)
}
