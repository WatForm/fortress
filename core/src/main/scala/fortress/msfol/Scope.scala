package fortress.msfol

import fortress.util.Errors


sealed trait Scope {
    def name: String
    def isBounded: Boolean
    override def toString: String = name
}

/* leave the sort unbounded */
case object UnboundedScope extends Scope {
    def name: String = "UnboundedScope"
    def isBounded = false
}

case class BoundedScope(value: Int, isExact: Boolean) extends Scope {
    def name: String = if(isExact) "ExactScope" else "NonExactScope"
    def isBounded = true
}

///* exact scope, like |A|=3 */
//case class ExactScope(scope: Int) extends BoundedScope {
//    Errors.Internal.precondition(scope > 0)
//    override def name: String = "ExactScope"
//    def isExact = true
//    override def value: Int = scope
//}
//
///* non-exact scope, like |A|<=3 */
//case class NonExactScope(scope: Int) extends BoundedScope {
//    Errors.Internal.precondition(scope > 0)
//    override def name: String = "NonExactScope"
//    def isExact = false
//    override def value: Int = scope
//}

object Scope {
    def mkBoundedScope(value: Int, isExact: Boolean): BoundedScope = {
        Errors.Internal.precondition(value > 0)
        BoundedScope(value, isExact)
    }

    val unbounded: Scope = UnboundedScope
}