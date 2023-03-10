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

//        int method =  Integer.parseInt(args[1]);
        String[] strs = args[0].split("/");

        FileWriter writer = new FileWriter(new File("/home/zxt/Desktop/project/fortress/test-results/" + strs[strs.length -1] +"-3Threads.txt" ));

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
//                    long t0 = System.currentTimeMillis();
//                    ModelFinderResult result1 = finder.checkSat(1);
//                    long t1 = System.currentTimeMillis();
//                    System.out.println("Satisiable?: " + result1.toString());
//                    System.out.println("Time: " + (t1-t0) + " ms");
//                    writer.write("Result: " + result1.toString() + "\n");
//                    writer.write("Time: " + (t1-t0) + " ms\n");
//
//                    if(result1.toString().equals("Sat")) {
//                        cnt++;
//                        totalTime += (t1 - t0);
//                    }
//                    System.out.println("--------------------------------------------------------------");
//                    long t2 = System.currentTimeMillis();
//                    ModelFinderResult result2 = finder.checkSat(false);
//                    long t3 = System.currentTimeMillis();
//                    System.out.println("Satisiable?: " + result2.toString());
//                    System.out.println("Time: " + (t3-t2) + " ms");
//
//                    if(result2.toString().equals("Sat")) {
//                        cnt++;
//                        totalTime += (t3 - t2);
//                    }

                    long t4 = System.currentTimeMillis();
                    ModelFinderResult result3 = finder.multiThreadCheckSat();
                    long t5 = System.currentTimeMillis();
                    writer.write("Result: " + result3.toString() + "\n");
                    writer.write("Time: " + (t5-t4) + " ms\n");
                    writer.flush();

                    if(result3.toString().equals("Sat")) {
                        cnt++;
                        totalTime += (t5 - t4);
                    }

//                    writer.write("Use monotonicity: " + result1.toString() + "   Time: " + (t1-t0) + " ms\n");
//                    writer.write("Not Use monotonicity: " + result2.toString() + "   Time: " + (t3-t2) + " ms\n");
//                    if(result1.toString().equals("Sat") && result2.toString().equals("Sat")) {
//                        if((t1-t0) < (t3-t2)) writer.write("Using Mono is better.\n");
//                        else writer.write("Not using Mono is better.\n");
//                    }
//                    else if(result1.toString().equals("Sat")) writer.write("Using Mono is better.\n");
//                    else if(result2.toString().equals("Sat")) writer.write("Not using Mono is better.\n");
//                    else writer.write("Bad result. :(\n");
                    writer.write("\n=====================================================================================\n");
                }
            }
        }
        writer.write("\nSolved " + cnt + " problems, used " + totalTime + " ms.\n");
        writer.close();
    }
}
