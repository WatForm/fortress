import fortress.msfol.*;
import static fortress.msfol.Term.*;
import fortress.msfol.Sort.*;
import fortress.msfol.FuncDecl.*;
import fortress.modelfind.*;

import java.util.*;
import java.util.stream.*;
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

        // Constants to be used instead of domain elements
        List<Var> distances = new ArrayList<>();
        Var dist1 = mkVar("dist1");
        Var dist2 = mkVar("dist2");
        distances.add(dist1);
        distances.add(dist2);
        List<AnnotatedVar> annotatedDistances = distances.stream()
            .map(v -> v.of(Distance))
            .collect(Collectors.toList());

        List<Var> positions = new ArrayList<>();
        for(int i=1; i <= size*size; ++i){
            positions.add(mkVar("pos" + i));
        }
        List<AnnotatedVar> annotatedPositions = positions.stream()
            .map(v -> v.of(Position))
            .collect(Collectors.toList());

        List<Var> indices = new ArrayList<>();
        for(int i=1; i <= size; ++i){
            indices.add(mkVar("idx" + i));
        }
        List<AnnotatedVar> annotatedIndices = indices.stream()
            .map(v -> v.of(Index))
            .collect(Collectors.toList());

        // Axioms
        List<Term> axioms = new ArrayList<>(5 + size * size * 2);
        axioms.add(mkDistinct(distances));
        axioms.add(mkDistinct(positions));
        axioms.add(mkDistinct(indices));
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
                        dist1),
                    mkEq(mkApp(dist, mkApp(col,pos), mkApp(col, mkApp(next,pos))),
                        dist2)
                ),
                mkAnd(
                    mkEq(mkApp(dist, mkApp(row,pos), mkApp(row, mkApp(next,pos))),
                        dist2),
                    mkEq(mkApp(dist, mkApp(col,pos), mkApp(col, mkApp(next,pos))),
                        dist1)
                )
            ));
        axioms.add(knightJump);

        // Define the distance function
        // (Distance has 3 values: 1 represents 1, 2 represents 2, and 3 represents invalid)
        for(int i = 0; i < size; ++i){
            for(int j = 0; j < size; ++j){
                int diff = abs(i - j);
                Term t;
                if(diff == 1 || diff == 2){
                    t = mkEq(mkApp(dist, indices.get(i), indices.get(j)),
                            distances.get(diff - 1));
                }
                else{
                    t = mkAnd(
                        mkNot(mkEq(mkApp(dist, indices.get(i), indices.get(j)),
                            dist1)),
                        mkNot(mkEq(mkApp(dist, indices.get(i), indices.get(j)),
                            dist2))
                    );
                }

                axioms.add(t);
            }
        }

        // Define the next function
        for(int i = 0; i + 1 < size * size ; ++i){
            Term t = mkEq(mkApp(next, positions.get(i)), positions.get(i + 1));
            axioms.add(t);
        }
        axioms.add(mkEq(mkApp(next, positions.get(positions.size()-1)), positions.get(0)));

        // Initialize the theory
        Theory knightsTheory =  Theory.empty()
            .withSorts(Position, Index, Distance)
            .withFunctionDeclarations(rowFn, colFn, nextFn, distFn)
            .withConstants(annotatedDistances)
            .withConstants(annotatedPositions)
            .withConstants(annotatedIndices)
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

        // Check if all axioms in the theory are satisfiable
        ModelFinderResult result = finder.checkSat();
        System.out.println("Satisiable?: " + result.toString());

        if(result.equals(ModelFinderResult.Sat())) {
            System.out.println(finder.viewModel());
            Map<List<Value>, Value> nextMap = finder.viewModel().functionInterpretationsJava().get(nextFn);
            Map<List<Value>, Value> rowMap = finder.viewModel().functionInterpretationsJava().get(rowFn);
            Map<List<Value>, Value> colMap = finder.viewModel().functionInterpretationsJava().get(colFn);
            Map<AnnotatedVar, Value> constants = finder.viewModel().constantInterpretationsJava();

            // utility map to help print indices
            Map<Value, Integer> indicesMap = new HashMap<>();
            for(int i=1; i <= size; ++i){
                indicesMap.put(constants.get(annotatedIndices.get(i-1)), i);
            }

            Value currPos = constants.get(annotatedPositions.get(0));
            for(int i=1; i<=size*size; ++i){
                Value currRow = rowMap.get(List.of(currPos));
                Value currCol = colMap.get(List.of(currPos));
                System.out.println("Position: " + i
                    + "\tRow: " + indicesMap.get(currRow)
                    + "\tCol:" + indicesMap.get(currCol));
                currPos = nextMap.get(List.of(currPos));
            }
        }
    }
}
