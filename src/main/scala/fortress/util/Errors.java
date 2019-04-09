package fortress.util;

import java.util.function.Supplier;
import java.lang.RuntimeException;
import java.lang.Deprecated;

// Inspiration:
// https://stackoverflow.com/questions/41323735/is-actively-throwing-assertionerror-in-java-good-practice
// https://github.com/google/guava/wiki/ConditionalFailuresExplained

public class Errors {
    
    static class PreconditionException extends RuntimeException {
        public PreconditionException(String message) {
            super(message);
        }
    }
    
    static class VerifyException extends RuntimeException {
        public VerifyException(String message) {
            super(message);
        }
    }
    
    static class AssertionException extends RuntimeException {
        public AssertionException(String message) {
            super(message);
        }
    }
    
    // Precondition: if failed, the method caller messed up
    public static void precondition(boolean condition) {
        if(!condition) {
            throw new PreconditionException("Precondition violated");
        }
    }
    
    public static void precondition(boolean condition, String message) {
        if(!condition) {
            throw new PreconditionException("Precondition violated: " + message);
        }
    }
    
    public static void precondition(boolean condition, Supplier<String> messageSupplier){
        precondition(condition, messageSupplier.get());
    }
    
    // Verification: I don't trust the output of some other function/API
    // and want to check it myself
    public static void verify(boolean condition) {
        if(!condition) {
            throw new VerifyException("Verify failed");
        }
    }
    
    public static void verify(boolean condition, String message) {
        if(!condition) {
            throw new VerifyException("Verify failed: " + message);
        }
    }
    
    public static void verify(boolean condition, Supplier<String> messageSupplier) {
        verify(condition, messageSupplier.get());
    }
    
    // Assertion: I want to check that I didn't mess up
    public static void assertion(boolean condition) {
        if(!condition) {
            throw new AssertionException("Assertion failed");
        }
    }
    
    public static void assertion(boolean condition, String message) {
        if(!condition) {
            throw new AssertionException("Assertion failed: " + message);
        }
    }
    
    public static void assertion(boolean condition, Supplier<String> messageSupplier) {
        assertion(condition, messageSupplier.get());
    }
    
    public static void assertUnreachable() {
        assertion(false, "Code should be unreachable");
    }
    
    public static <T> T notImplemented() {
        throw new scala.NotImplementedError();
    }
}
