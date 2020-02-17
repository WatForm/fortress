package fortress.inputs;

import fortress.msfol.*;
import java.io.*;

public interface TheoryParser {
    
    public abstract Theory parse(InputStream inputStream) throws IOException;

}
