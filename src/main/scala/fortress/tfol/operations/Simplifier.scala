package fortress.tfol.operations

import fortress.tfol._

object Simplifier {
    def apply(term: Term): Term = {
        def simplify1(term: Term): Term = term match {
            case Not(Bottom()) => Top()
            case Not(Top()) => Bottom()
            case Not(Not(body)) => body
            case AndList(args) => {
                if (args.exists(t => t == Bottom()))
                    Bottom()
                else {
                    val newArgs = args.filter(t => t != Top())
                    if (newArgs.size == 0) Top() else AndList(newArgs)
                }
            }
            case OrList(args) => {
                if (args.exists(t => t == Top()))
                    Top()
                else {
                    val newArgs = args.filter(t => t != Bottom())
                    if (newArgs.size == 0) Bottom() else OrList(newArgs)
                }
            }
            case Implication(Bottom(), _) => Top()
            case Implication(_, Top()) => Top()
            case Implication(Top(), p) => p
            case Implication(p, Bottom()) => Not(p)
            case Iff(p, Top()) => p
            case Iff(Top(), p) => p
            case Iff(p, Bottom()) => Not(p)
            case Iff(Bottom(), p) => Not(p)
            case Eq(left, right) => if (left == right) Top() else term
            // Note that we don't need a signature to check below whether the free
            // free variable is really or a constant. We just want to check if
            // the quantified variable x is within the set of free vars.
            // If x is within free vars union constants, then since it is quantified
            // here it must be a free var.
            case Exists(vars, body) => {
                val freeVars: java.util.Set[Var] = body.freeVarConstSymbols
                val newVars = vars.filter((av: AnnotatedVar) => freeVars.contains(av.variable))
                if (newVars.size == 0)
                    body
                else
                    Exists(newVars, body)
            }
            case Forall(vars, body) => {
                val freeVars: java.util.Set[Var] = body.freeVarConstSymbols
                val newVars = vars.filter((av: AnnotatedVar) => freeVars.contains(av.variable))
                if (newVars.size == 0)
                    body
                else
                    Forall(newVars, body)
            }
            case _ => term
        }
        
        def simplify(term: Term): Term = term match {
            case Not(body) => simplify1(Not(simplify(body)))
            case AndList(args) => simplify1(AndList(args.map(simplify)))
            case OrList(args) => simplify1(OrList(args.map(simplify)))
            case Implication(left, right) => simplify1(Implication(simplify(left), simplify(right)))
            case Iff(left, right) => simplify1(Iff(simplify(left), simplify(right)))
            case Eq(left, right) => simplify1(Eq(simplify(left), simplify(right)))
            case App(fname, args) => simplify1(App(fname, args.map(simplify)))
            case Exists(vars, body) => simplify1(Exists(vars, simplify(body)))
            case Forall(vars, body) => simplify1(Forall(vars, simplify(body)))
            case _ => term
        }
        
        simplify(term)
    }
}