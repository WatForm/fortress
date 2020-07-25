/* Parse SMT-LIB2 file given as command-line arg,
   set scopes to default value,
   run model finder,
   and output results */

import fortress.msfol.*;
import fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.inputs.*;
import fortress.modelfind.*;

import java.util.*;
import java.io.*;

public class Smtlibparsemain {

    public static void main(String[] args) throws Exception {

        if (args.length == 0) {
            System.out.println("Missing Argument");
            System.exit(1);
        }
        String inputFilePath = args[0];
	    if (!inputFilePath.endsWith(".smt2")) {
            System.out.println("Argument must be .smt2 file");
            System.exit(1);
        }

	    File f = new File(inputFilePath);
	    Integer scope = 2;
	    Integer thresholdTimeout = 10000; // milliseconds
	    FileInputStream fileStream ;

 		try(ModelFinder modelfinder = ModelFinder.createDefault()) {
			fileStream = new FileInputStream(f);
	        // parse SMT-LIB to Fortress theory
	        SmtLibParser parser = new SmtLibParser();
	        Theory thy = parser.parse(fileStream);
	        // Set up model finder
			modelfinder.setTimeout(thresholdTimeout);
			modelfinder.setTheory(thy);
			// Set all sorts to default scopes
			for (Sort s: thy.sortsJava())  {
				if (!(s.isBuiltin())) {
					modelfinder.setAnalysisScope(s,scope);
				}
			}

	        Writer log = new PrintWriter(System.out);
	    	modelfinder.setOutput(log);

			// run until hits timeout rather than try to time this process?
	    	ModelFinderResult result = modelfinder.checkSat();
	    	System.out.println(inputFilePath);
	    	System.out.println("Scope is "+scope);
	    	System.out.println(result);
	    } catch (FileNotFoundException e) {
	    	System.out.println(inputFilePath+" not found.") ;
	    	System.exit(1) ;
        }
    }
}
