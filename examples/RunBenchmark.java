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

        int id = Integer.parseInt(args[1]);
        String[] strs = args[0].split("/");

        String[] methods = new String[] {
                "RSV",
                "Mono-RSV",
                "NonExactScope",
                "Mono-NonExactScope",
                "3threads"
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

                ModelFinder finder = null;
                if(id == 0) finder = ModelFinder.RSVModelFinder();
                if(id == 1) finder = ModelFinder.MonoRSVModelFinder();
                if(id == 2) finder = ModelFinder.NonExactScopeModelFinder();
                if(id == 3) finder = ModelFinder.MonoNonExactScopeModelFinder();
                if(id == 4) finder = ModelFinder.multiThreadsModelFinder();

                finder.setTheory(theory);

                long t1 = System.currentTimeMillis();
                ModelFinderResult result = finder.checkSat();
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
        writer.write("\nSolved " + cnt + " problems, used " + totalTime + " ms.\n");
        writer.close();
    }
}
