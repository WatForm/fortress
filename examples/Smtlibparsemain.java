/* Parse SMT-LIB file given as input, set scopes to default value, run model finder, and output results */
import fortress.msfol.*;
import fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.inputs.*;
import fortress.modelfind.*;

import java.util.*;
import java.io.*;

import org.apache.commons.cli.*;

public class Smtlibparsemain {

    public static void main(String[] args) throws Exception {

        if args.length == 0 {
            System.out.println("Missing Argument");
            System.exit(1);
        }
        String inputFilePath = args[0];
	    if (!inputFilePath.lowercaseName.endsWith(".smt")) {
            System.out.println("Argument must be .smt file");
            System.exit(1);
        }

	    File f = new File(inputFilePath);
	    Integer scope = 5;
	    Integer thresholdTimeout = 10000; // milliseconds
 
 		try {
	        FileInputStream fileStream = new FileInputStream(f); 
	    } catch (FileNotFoundException e) {
	    	System.out.println(inputFilePath+" not found.")
	    	System.exit(1)
        }
        // parse SMT-LIB to Fortress theory      
        SmtLibParser parser = new SmtLibParser();	
        Theory thy = parser.parse(fileStream);
        // Set up model finder
        ModelFinder modelfinder = ModelFinder.createDefault();
		modelfinder.setTimeout(thresholdTimeout);
		modelfinder.setTheory(thy);
		// Set all sorts to default scopes
		for (Sort s: thy.sortsJava())  {
			// s.isBuiltIn()
			if (!s.isBuiltIn()) {
				modelfinder.setAnalysisScope(s,scope);
			} else {
				// Built-in type
				if !(s.equals(Sort.Bool())) {
					// something special for Int or other built-in types
				}
			}
		}

        Writer log = new PrintWriter(System.out);
    	modelfinder.setOutput(log);

		// run until hits timeout rather than try to time this process?
    	ModelFinderResult result = modelfinder.checkSat();
    	System.out.println(inputFilePath);
    	System.out.println("Scope is "+scope);
    	System.out.println(result);
    }
}
//	        } catch (FileNotFoundException e) {
//	            e.printStackTrace();
//	        } catch (IOException e) {
//	            e.printStackTrace();
//	        } 
