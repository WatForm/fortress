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
        class DoesNotExistError(message: String) extends Error(message)

        class transformerDoesNotExist(message:String) extends Error(message) 
        def transformerDoesNotExist(message:String): Unit = 
            throw new transformerDoesNotExist(message)

        class modelFinderDoesNotExist(message:String) extends Error(message)
        def modelFinderDoesNotExist(message:String): Unit = 
            throw new modelFinderDoesNotExist(message)
 
        class compilerDoesNotExist(message:String) extends Error(message)
        def compilerDoesNotExist(message:String): Unit = 
            throw new compilerDoesNotExist(message)

        class solverDoesNotExist(message:String) extends Error(message)
        def solverDoesNotExist(message:String): Unit = 
            throw new solverDoesNotExist(message)

        def doesNotExist(message: String) = throw new DoesNotExistError("Does Not Exist Error: " + message)
        // API errors are when the user of the API does something wrong - these can be catchable Exceptions

        class CliError(message: String) extends Error(message)
        def cliError(message: String) = throw new CliError("CLI Error: " + message)

        def checkCliInput(condition: Boolean, message: String): Unit = 
            if (!condition) cliError(message) else ()



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
}
