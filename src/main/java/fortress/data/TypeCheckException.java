package fortress.data;

import java.lang.RuntimeException;

public class TypeCheckException extends RuntimeException {
    public TypeCheckException(String message) {
        super(message);
    }
}
