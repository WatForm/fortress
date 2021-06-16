package fortress.inputs;

import fortress.msfol.*;
import fortress.util.Errors;
import scala.util.Either;

import java.io.*;

public interface TheoryParser {
    
    public abstract Either<Errors.ParserError, Theory> parse(InputStream inputStream) throws IOException;

    public abstract  Either<Errors.ParserError, Theory> parse(String filePath) throws IOException;

}
