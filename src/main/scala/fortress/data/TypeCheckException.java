package fortress.data;

import java.lang.RuntimeException;

public abstract class TypeCheckException extends RuntimeException {
    protected TypeCheckException(String message) {
        super(message);
    }
    
    // These different subclasses exist to facilitate testing
    // This way we can test that typechecking fails for the reason we expect
    
    public static class NameConflict extends TypeCheckException {
        public NameConflict(String message) {
            super(message);
        }
    }
    
    public static class UnknownType extends TypeCheckException {
        public UnknownType(String message) {
            super(message);
        }
    }
    
    public static class UndeterminedType extends TypeCheckException {
        public UndeterminedType(String message) {
            super(message);
        }
    }
    
    public static class UnknownFunction extends TypeCheckException {
        public UnknownFunction(String message) {
            super(message);
        }
    }
    
    public static class WrongArgType extends TypeCheckException {
        public WrongArgType(String message) {
            super(message);
        }
    }
    
    public static class WrongArity extends TypeCheckException {
        public WrongArity(String message) {
            super(message);
        }
    }
    
    public static class BadStructure extends TypeCheckException {
        public BadStructure(String message) {
            super(message);
        }
    }
}
