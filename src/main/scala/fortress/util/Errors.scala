package fortress.util

import java.util.function.Supplier
import java.lang.AssertionError

// Inspiration:
// https://stackoverflow.com/questions/41323735/is-actively-throwing-assertionerror-in-java-good-practice
// https://github.com/google/guava/wiki/ConditionalFailuresExplained

object Errors {

    // TODO Should distinguish between internal preconditions (which would throw errors) and public preconditions (which should throw exceptions)
    
    class PreconditionException(message: String) extends RuntimeException(message)
    
    class DebugException(message: String) extends RuntimeException(message)
    
    class UnsupportedException(message: String) extends RuntimeException(message)
    
    class SolverException(message: String) extends RuntimeException(message)
    
    // Precondition: if failed, the method caller messed up
    def precondition(condition: Boolean): Unit = {
        if(!condition) {
            throw new PreconditionException("Precondition violated")
        }
    }
    
    def precondition(condition: Boolean, message: => String): Unit = {
        if(!condition) {
            throw new PreconditionException("Precondition violated: " + message)
        }
    }

    def preconditionFailed[T](message: String): T = {
        throw new PreconditionException(message)
    }
    
    // Assertion: I want to check that I didn't mess up
    def assertion(condition: Boolean): Unit = {
        if(!condition) {
            throw new AssertionError("Assertion failed")
        }
    }
    
    def assertion(condition: Boolean, message: => String): Unit = {
        if(!condition) {
            throw new AssertionError("Assertion failed: " + message)
        }
    }
    
    def impossibleState: Nothing = throw new AssertionError("This program state should be impossible.")
    def impossibleState(message: String): Nothing = throw new AssertionError("This program state should be impossible: " + message)
    
    def unsupported[T](message: String): T = {
        throw new UnsupportedException("Unuspported: " + message)
    }
    
    def solverError(message: String): Unit = {
        throw new SolverException("Solver exception: " + message)
    }
}
