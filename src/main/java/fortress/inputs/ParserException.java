package fortress.inputs;

import java.lang.RuntimeException;
import java.lang.Throwable;

public class ParserException extends RuntimeException {
    public ParserException(String msg) {
        super(msg);
    }
    
    public ParserException(Throwable cause) {
        super(cause);
    }
}
