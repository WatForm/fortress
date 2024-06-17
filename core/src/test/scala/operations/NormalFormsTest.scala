import fortress.msfol._
import fortress.operations.NormalForms

class NormalFormsTest extends UnitSuite with CommonSymbols {

    val miniscopeTable: Seq[(Term, Term)] = Seq(
        (Top, Top),
        (Bottom, Bottom),
        (x, x),

        (Forall(x of A, Top), Top),
        (Forall(x of A, f(x)), Forall(x of A, f(x))),
        (Forall(x of A, And(f(x), g(x))), And(Forall(x of A, f(x)), Forall(x of A, g(x)))),
        (Forall(x of A, And(f(x), g(y))), And(Forall(x of A, f(x)), g(y))),
        (Forall(x of A, And(g(y), f(x))), And(g(y), Forall(x of A, f(x)))),
        (Forall(x of A, And(f(y), g(z))), And(f(y), g(z))),
        (Forall(x of A, Or(f(x), g(x))), Forall(x of A, Or(f(x), g(x)))),
        (Forall(x of A, Or(f(x), g(y))), Or(g(y), Forall(x of A, f(x)))),
        (Forall(x of A, Or(g(y), f(x))), Or(g(y), Forall(x of A, f(x)))),
        (Forall(x of A, Or(f(y), g(z))), Or(f(y), g(z))),
        (Forall(x of A, And(Or(f(x), g(y)), Or(g(x), f(y)))),
            And(Or(g(y), Forall(x of A, f(x))), Or(f(y), Forall(x of A, g(x))))),
        (Forall(x of A, Forall(y of A, f(x,y))), Forall(Seq(x of A, y of A), f(x,y))),
        (Forall(Seq(x of A, y of A), And(f(x), f(y))), And(Forall(x of A, f(x)), Forall(y of A, f(y)))),
        (Forall(Seq(x of A, y of A), Or(f(x), f(y))), Or(Forall(y of A, f(y)), Forall(x of A, f(x)))),
        (Forall(Seq(x of A, y of A), Or(f(x), f(x,y), g(x,y))),
            Forall(x of A, Or(f(x), Forall(y of A, Or(f(x,y), g(x,y)))))),
        (Forall(x of A, And(Forall(y of A, And(f(x), g(y))), Forall(y of A, And(f(x), g(y))))),
            And(And(Forall(x of A, f(x)), Forall(y of A, g(y))), And(Forall(x of A, f(x)), Forall(y of A, g(y))))),
        (Forall(x of A, Exists(y of A, f(x,y))), Forall(x of A, Exists(y of A, f(x,y)))),
        (Forall(x of A, Exists(y of A, And(f(x), g(y)))),
            And(Forall(x of A, f(x)), Forall(x of A, Exists(y of A, g(y))))), // redundant because no scope sorting
        (Forall(x of A, Exists(y of A, Or(f(x,y), g(x,y)))),
            Forall(x of A, Or(Exists(y of A, f(x,y)), Exists(y of A, g(x,y))))),

        (Exists(x of A, Top), Top),
        (Exists(x of A, f(x)), Exists(x of A, f(x))),
        (Exists(x of A, Or(f(x), g(x))), Or(Exists(x of A, f(x)), Exists(x of A, g(x)))),
        (Exists(x of A, Or(f(x), g(y))), Or(Exists(x of A, f(x)), g(y))),
        (Exists(x of A, Or(g(y), f(x))), Or(g(y), Exists(x of A, f(x)))),
        (Exists(x of A, Or(f(y), g(z))), Or(f(y), g(z))),
        (Exists(x of A, And(f(x), g(x))), Exists(x of A, And(f(x), g(x)))),
        (Exists(x of A, And(f(x), g(y))), And(g(y), Exists(x of A, f(x)))),
        (Exists(x of A, And(g(y), f(x))), And(g(y), Exists(x of A, f(x)))),
        (Exists(x of A, And(f(y), g(z))), And(f(y), g(z))),
        (Exists(x of A, Or(And(f(x), g(y)), And(g(x), f(y)))),
            Or(And(g(y), Exists(x of A, f(x))), And(f(y), Exists(x of A, g(x))))),
        (Exists(x of A, Exists(y of A, f(x,y))), Exists(Seq(x of A, y of A), f(x,y))),
        (Exists(Seq(x of A, y of A), Or(f(x), f(y))), Or(Exists(x of A, f(x)), Exists(y of A, f(y)))),
        (Exists(Seq(x of A, y of A), And(f(x), f(y))), And(Exists(y of A, f(y)), Exists(x of A, f(x)))),
        (Exists(Seq(x of A, y of A), And(f(x), f(x,y), g(x,y))),
            Exists(x of A, And(f(x), Exists(y of A, And(f(x,y), g(x,y)))))),
        (Exists(x of A, Or(Exists(y of A, Or(f(x), g(y))), Exists(y of A, Or(f(x), g(y))))),
            Or(Or(Exists(x of A, f(x)), Exists(y of A, g(y))), Or(Exists(x of A, f(x)), Exists(y of A, g(y))))),
        (Exists(x of A, Forall(y of A, f(x,y))), Exists(x of A, Forall(y of A, f(x,y)))),
        (Exists(x of A, Forall(y of A, Or(f(x), g(y)))),
            Or(Exists(x of A, f(x)), Exists(x of A, Forall(y of A, g(y))))), // redundant because no scope sorting
        (Exists(x of A, Forall(y of A, And(f(x,y), g(x,y)))),
            Exists(x of A, And(Forall(y of A, f(x,y)), Forall(y of A, g(x,y))))),

        // Example from Lampert (https://www2.cms.hu-berlin.de/newlogic/webMathematica/Logic/minimizingDNFFOL.pdf)
        (Exists(y of A, Forall(x of A, And(Or(And(Not(R(x,x)), S(y)), Q(x,y)), p))),
            And(p, Exists(y of A, Forall(x of A, Or(And(Not(R(x,x)), S(y)), Q(x,y)))))),
    )

    miniscopeTable foreach { case (input, output) =>
        test(f"miniscope: $input => $output") {
            NormalForms.miniscope(input) should be(output)
        }
    }

}
