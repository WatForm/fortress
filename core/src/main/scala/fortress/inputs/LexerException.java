package fortress.inputs;

import java.lang.RuntimeException;
import java.lang.Throwable;

public class LexerException extends RuntimeException {
    public LexerException(String msg) {
        super(msg);
    }
    
    public LexerException(Throwable cause) {
        super(cause);
    }
}
