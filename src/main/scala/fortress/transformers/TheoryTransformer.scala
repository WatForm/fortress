package fortress.transformers

import scala.language.implicitConversions
import fortress.msfol.{Theory, Problem}

/** An abstraction of a function from Theory to Theory. */
trait TheoryTransformer {
    
    /** Takes in a theory, applies some transformation to it, and produces a
    * new theory. Note that this does not mutate the theory object, only
    * produces a new one. */
    def apply(theory: Theory): Theory
    
    def name: String
}

object TheoryTransformer {
    implicit def asProblemTransformer(theoryTransformer: TheoryTransformer): ProblemTransformer = {
        object asPT extends ProblemTransformer {
            override def apply(problem: Problem): Problem = problem match {
                case Problem(theory, scopes) => Problem(theoryTransformer(theory), scopes)
            }
            
            override def name = theoryTransformer.name
        }
        asPT
    }
}
