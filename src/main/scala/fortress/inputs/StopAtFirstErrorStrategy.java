package fortress.inputs;

import org.antlr.v4.runtime.DefaultErrorStrategy;
import org.antlr.v4.runtime.Parser;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.InputMismatchException;
import org.antlr.v4.runtime.Token;

public class StopAtFirstErrorStrategy extends DefaultErrorStrategy {
	 
    @Override
    public void recover(Parser recognizer, RecognitionException e) {
        throw new ParserException(e);
    }

    @Override
    public Token recoverInline(Parser recognizer) throws RecognitionException {
        throw new ParserException(new InputMismatchException(recognizer));
    }

    @Override
    public void sync(Parser recognizer) {
        // do nothing
    }
}
