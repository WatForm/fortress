import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.*;
import static java.lang.Math.abs;

public class KnightsTour{
    public static void main(String[] args){
        if(args.length < 1) {
            System.err.println("Please include grid size");
            System.exit(1);
        }
        int size = Integer.parseInt(args[0]);
        int timeout = args.length >= 2 ? Integer.parseInt(args[1]) : 30000;

        // Define Sorts
        Sort Position = Sort.mkSortConst("Position");
        Sort Index = Sort.mkSortConst("Index");
        Sort Distance = Sort.mkSortConst("Distance");

        // Function Names
        final String row = "row";
        final String col = "col";
        final String next = "next";
        final String dist = "dist";

        // row: Position -> Index
        FuncDecl rowFn = FuncDecl.mkFuncDecl(row, Position, Index);
        // col: Position -> Index
        FuncDecl colFn = FuncDecl.mkFuncDecl(col, Position, Index);
        // next: Position -> Position
        FuncDecl nextFn = FuncDecl.mkFuncDecl(next, Position, Position);
        // dist: Index X Index -> Distance
        FuncDecl distFn = FuncDecl.mkFuncDecl(dist, Index, Index, Distance);

        // Variable declarations to use with quantifiers
        Var pos = mkVar("pos");
        Var pos1 = mkVar("pos1");
        Var pos2 = mkVar("pos2");

        // Axioms
        List<Term> axioms = new ArrayList<>(2 + size * size * 2);
        // Unique Positions
        Term uniquePositions = mkForall(List.of(pos1.of(Position), pos2.of(Position)),
            mkImp(
                mkAnd(
                    mkEq(mkApp(row,pos1), mkApp(row, pos2)),
                    mkEq(mkApp(col,pos1), mkApp(col, pos2))
                ),
                mkEq(pos1, pos2)
            ));
        axioms.add(uniquePositions);

        // Knight jumps with a distance of 1 in one direction and a distance of 2 in the other
        Term knightJump = mkForall(pos.of(Position),
            mkOr(
                mkAnd(
                    mkEq(mkApp(dist, mkApp(row,pos), mkApp(row, mkApp(next,pos))),
                        mkDomainElement(1, Distance)),
                    mkEq(mkApp(dist, mkApp(col,pos), mkApp(col, mkApp(next,pos))),
                        mkDomainElement(2, Distance))
                ),
                mkAnd(
                    mkEq(mkApp(dist, mkApp(row,pos), mkApp(row, mkApp(next,pos))),
                        mkDomainElement(2, Distance)),
                    mkEq(mkApp(dist, mkApp(col,pos), mkApp(col, mkApp(next,pos))),
                        mkDomainElement(1, Distance))
                )
            ));
        axioms.add(knightJump);

        // Define the distance function
        // (Distance has 3 values: 1 represents 1, 2 represents 2, and 3 represents invalid)
        for(int i = 1; i <= size; ++i){
            for(int j = 1; j <= size; ++j){
                int diff = abs(i - j);
                Term t = mkEq(mkApp(dist, mkDomainElement(i, Index), mkDomainElement(j, Index)),
                            mkDomainElement(diff == 1 || diff == 2 ? diff : 3, Distance));
                axioms.add(t);
            }
        }

        // Define the next function
        for(int i = 1; i < size * size ; ++i){
            Term t = mkEq(mkApp(next, mkDomainElement(i, Position)), mkDomainElement(i + 1, Position));
            axioms.add(t);
        }
        axioms.add(mkEq(mkApp(next, mkDomainElement(size * size, Position)), mkDomainElement(1, Position)));

        // Initialize the theory
        Theory knightsTheory =  Theory.empty()
            .withSorts(Position, Index, Distance)
            .withFunctionDeclarations(rowFn, colFn, nextFn, distFn)
            .withAxioms(axioms);

        // Initialize a model finder
        ModelFinder finder = ModelFinder.createDefault();

        finder.setTimeout(timeout);

        // Set the theory of the model finder
        finder.setTheory(knightsTheory);

        // Set the scopes of the model finder
        finder.setAnalysisScope(Index, size);
        finder.setAnalysisScope(Position, size*size);
        finder.setAnalysisScope(Distance, 3);

        // utility map to help print indices
        Map<Value, Integer> indices = new HashMap<>();
        for(int i=1; i <= size; ++i){
            indices.put(mkDomainElement(i, Index), i);
        }

        // Check if all axioms in the theory are satisfiable
        ModelFinderResult result = finder.checkSat();
        System.out.println("Satisiable?: " + result.toString());

        if(result.equals(ModelFinderResult.Sat())) {
            System.out.println(finder.viewModel());
            Map<List<Value>, Value> nextMap = finder.viewModel().functionInterpretationsJava().get(nextFn);
            Map<List<Value>, Value> rowMap = finder.viewModel().functionInterpretationsJava().get(rowFn);
            Map<List<Value>, Value> colMap = finder.viewModel().functionInterpretationsJava().get(colFn);
            Value currPos = mkDomainElement(1, Position);
            for(int i=1; i<=size*size; ++i){
                Value currRow = rowMap.get(List.of(currPos));
                Value currCol = colMap.get(List.of(currPos));
                System.out.println("Position: " + i
                    + "\tRow: " + indices.get(currRow)
                    + "\tCol:" + indices.get(currCol));
                currPos = nextMap.get(List.of(currPos));
            }
        }
    }
}
