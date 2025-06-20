package fortress.util

import java.util.function.Supplier
import java.lang.AssertionError
import java.lang.Error

// Inspiration:
// https://stackoverflow.com/questions/41323735/is-actively-throwing-assertionerror-in-java-good-practice
// https://github.com/google/guava/wiki/ConditionalFailuresExplained

// When using errors, try use the most detailed error that you can
// If nothing seems appropriate, consider creating a new error
object Errors {

    object API {
        case class DoesNotExistError(message: String) extends Error(message)

        case class transformerDoesNotExist(message:String) extends Error(message) 
 
    
        case class modelFinderDoesNotExist(message:String) extends Error(message)

 
        case class compilerDoesNotExist(message:String) extends Error(message)

        case class solverDoesNotExist(message:String) extends Error(message)


        def doesNotExist(message: String) = throw new DoesNotExistError("Does Not Exist Error: " + message)
        // API errors are when the user of the API does something wrong - these can be catchable Exceptions

 
    }

    // for the CLI, we don't throw exceptions, but give an error message and exit
    def cliError(message:String) {
        System.err.println(message)
        System.exit(1)
    }

    object Internal {
        // Internal errors are Errors in the Java sense - they signify a significant problem and should not be caught

        // Preconditions
        class PreconditionError(message: String) extends AssertionError(message)

        def precondition(condition: Boolean): Unit = {
            if(!condition) {
                throw new PreconditionError("Precondition violated")
            }
        }
        
        def precondition(condition: Boolean, message: => String): Unit = {
            if(!condition) {
                throw new PreconditionError("Precondition violated: " + message)
            }
        }

        def preconditionFailed(message: String): Nothing = throw new PreconditionError(message)
        
        // Assertions
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
        
        // Other

        class SolverError(message: String) extends Error(message)
        def solverError(message: String): Unit = throw new SolverError("Solver error: " + message)
    }

    // Internal error used in parser java code
    class ParserError(message: String) extends Error(message)

    // Unsupported

    class UnsupportedFeature(message: String) extends Error(message)
}
