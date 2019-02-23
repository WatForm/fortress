package fortress.formats;

import fortress.tfol.*;
import fortress.util.Errors;
import fortress.sexpr.*;
import java.util.List;
import java.util.zip.DataFormatException;

public class SExprsToTheory {
    
    // // TODO object or static method?
    // private Theory theory;
    // List<Axiom> axioms;
    // 
    // public SExprsToTheory() {
    // }
    // 
    // public Theory convert(List<SExpr> sexprs) throws DataFormatException {
    //     theory = new Theory();
    // 
    //     for(SExpr sexpr : sexprs) {
    //         sexpr.match(
    //             (Atom atom) -> throw new DataFormatException("Atom at top level: " + atom.toString()),
    //             (ListExpr list) -> {
    //                 List<SExpr> subexpressions = list.getSubexpressions();
    //                 if(subexpressions.size() == 1) {
    //                     handleSingleArgCommand(subexpressions.get(0));
    //                 } else if(subexpressions.size() == 2) {
    //                     handleDoubleArgCommand(subexpressions.get(0), subexpressions.get(1));
    //                 }
    //             }
    // 
    //     }
    // }
    // 
    // public void handleSingleArgCommand(SExpr expr) {
    //     expr.match(
    //         (Atom atom) -> {
    // 
    //         },
    //         (ListExpr list) -> throw new DataFormatException("")
    //     )
    // }
}
