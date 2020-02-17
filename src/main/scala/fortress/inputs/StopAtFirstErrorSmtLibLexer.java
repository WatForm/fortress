package fortress.inputs;

import org.antlr.v4.runtime.*;
import java.lang.RuntimeException;

public class StopAtFirstErrorSmtLibLexer extends SmtLibSubsetLexer {
    
    public StopAtFirstErrorSmtLibLexer(CharStream input) {
        super(input);
    }
    
    @Override
    public void recover(LexerNoViableAltException e) {
        throw new LexerException(e); // Give up
    }
}
