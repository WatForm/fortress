import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;
import fortress.inputs.*;
import fortress.compiler.*;
import fortress.transformers.*;
import fortress.operations.*;
import fortress.interpretation.*;

import java.util.List;
import java.util. ArrayList;
import java.util.Map;
import java.io.*;


public class RunBenchmark {
    public static void main(String[] args) throws IOException {

        ArrayList<String> files = new ArrayList<String>();
        File file = new File(args[0]);
        File[] tempList = file.listFiles();
        long totalTime = 0;
        int cnt = 0;

    /*
        method = 0/1/2/3
        method = 0:  Monotonicity checking + RSVIncrementalSolving
        method = 1: RSVIncrementalSolving
        method = 2: Non-exact Scope solving (size = 5, 6, 7...)
        method = 3: Monotonicity checking + Non-exact Scope Solving
        method = 4: 4-threads
     */
        int id = Integer.parseInt(args[1]);
        String[] strs = args[0].split("/");

        String[] methods = new String[] {
                "Mono-RSV",
                "RSV",
                "NonExactScope",
                "Mono-NonExactScope",
                "4threads"
        };


        FileWriter writer = new FileWriter(new File("/home/zxt/Desktop/毕设/test-results/Fortress/" + strs[strs.length -1] + "-" + methods[id] + ".txt" ));

        for (int i = 0; i < tempList.length; i++) {
            if (tempList[i].isFile()) {
                System.out.println("=====================================================================================");
                System.out.println("file: " + tempList[i].toString() );
                writer.write("File: " + tempList[i].toString() + "\n");
                TheoryParser parser = new SmtLibParser();
                Object t = parser.parse(new FileInputStream(tempList[i].toString()));
                Theory theory = null;

                if(t instanceof scala.util.Right) {
                    theory = (Theory)(((scala.util.Right)t).right().get());
                } else {
                    System.err.println("Parse error");
                    System.exit(1);
                }

                try(ModelFinder finder = ModelFinder.IncrementalModelFinder()) {
                    finder.setTheory(theory);
                    long t1 = System.currentTimeMillis();
                    ModelFinderResult result = id==4 ? finder.multiThreadCheckSat() : finder.checkSat(id);
                    long t2 = System.currentTimeMillis();
                    writer.write("Result: " + result.toString() + "\n");
                    writer.write("Time: " + (t2-t1) + " ms\n");
                    writer.flush();

                    if(result.toString().equals("Sat")) {
                        cnt++;
                        totalTime += (t2 - t1);
                    }
                    writer.write("\n=====================================================================================\n");
                }
            }
        }
        writer.write("\nSolved " + cnt + " problems, used " + totalTime + " ms.\n");
        writer.close();
    }
}
