package fortress.operations

import fortress.msfol._
import fortress.util.Errors

object NormalForms {
    /** Returns the negation normal form of a term. 
      * It is assumed that Eq is not used on sort Bool and so uses of Eq are atomic.
      * Additionally it is assumed that applications and arguments to applications
      * are atomic. */
    def nnf(term: Term): Term = term match {
        case AndList(args) => AndList(args.map(nnf))
        case OrList(args) => OrList(args.map(nnf))
        case (distinct: Distinct) => nnf(distinct.asPairwiseNotEquals)
        case Implication(p, q) => OrList(nnf(Not(p)), nnf(q))
        case Iff(p, q) => OrList(
            AndList(nnf(p), nnf(q)),
            AndList(nnf(Not(p)), nnf(Not(q)))
        )
        case Forall(vars, body) => Forall(vars, nnf(body))
        case Exists(vars, body) => Exists(vars, nnf(body))
        case Not(Top) => Bottom
        case Not(Bottom) => Top
        case Not(Not(p)) => nnf(p)
        case Not(AndList(args)) => OrList(args.map(arg => nnf(Not(arg))))
        case Not(OrList(args)) => AndList(args.map(arg => nnf(Not(arg))))
        case Not(distinct @ Distinct(_)) => nnf(Not(distinct.asPairwiseNotEquals))
        case Not(Implication(p, q)) => AndList(nnf(p), nnf(Not(q)))
        case Not(Iff(p, q)) => OrList(
            AndList(nnf(p), nnf(Not(q))),
            AndList(nnf((Not(p))), nnf(q))
        )
        case Not(Forall(vars, body)) => Exists(vars, nnf(Not(body)))
        case Not(Exists(vars, body)) => Forall(vars, nnf(Not(body)))
        case App(fname, args) => App(fname, args map nnf)
        case Not(App(fname, args)) => Not(App(fname, args map nnf)) 

        case Closure(fname, arg1, arg2, args) => Closure(fname, nnf(arg1), nnf(arg2), args.map(nnf))
        case Not(Closure(fname, arg1, arg2, args)) => Not(Closure(fname, nnf(arg1), nnf(arg2), args.map(nnf)))
        case ReflexiveClosure(fname, arg1, arg2, args) => ReflexiveClosure(fname, nnf(arg1), nnf(arg2), args.map(nnf))
        case Not(ReflexiveClosure(fname, arg1, arg2, args)) => Not(ReflexiveClosure(fname, nnf(arg1), nnf(arg2), args.map(nnf)))
            
        case Eq(l, r) => Eq(nnf(l), nnf(r))
        case Not(Eq(l, r)) => Not(Eq(nnf(l), nnf(r))) // Not that Eq does not compare booleans
        case Top | Bottom | Var(_) | BuiltinApp(_, _) | DomainElement(_, _)
            | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
            | Not(Var(_)) | Not(BuiltinApp(_, _)) => term
        case Not(DomainElement(_, _)) | Not(IntegerLiteral(_))
            |  Not(BitVectorLiteral(_, _)) | Not(EnumValue(_)) => Errors.Internal.preconditionFailed(s"Term is not well-sorted: ${term}")
        case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(nnf(condition), nnf(ifTrue), nnf(ifFalse))
        case Not(IfThenElse(condition, ifTrue, ifFalse)) => Errors.Internal.preconditionFailed(s"Term is not santitized, ite cannot return Boolean: ${term}")
    }

    def prenex(term: Term): Term = ???

    /*
        Eliminate "ite", for If A then B else C
        i) if B,C are booleans ===> A & B | !A & C
        ii) else, there should be statement like "X = (If A then B else C)" ===> A & X=B | !A & X!=B
     */
    def iteEliminator(term: Term): Term = term match {
        case Forall(vars, body) => Forall(vars, iteEliminator(body))
        case Exists(vars, body) => Exists(vars, iteEliminator(body))
        case Implication(p, q) => Implication(iteEliminator(p), iteEliminator(q))
        case Iff(p, q) => Iff(iteEliminator(p), iteEliminator(q))
        case App(f, args) => App(f, args.map(iteEliminator))
        case Not(body) => Not(iteEliminator(body))
        case AndList(args) => AndList(args.map(iteEliminator))
        case OrList(args) => OrList(args.map(iteEliminator))
        case Eq(IfThenElse(a, b, c), r) =>
            iteEliminator(
                OrList(AndList(a, Eq(r, b)), AndList(Not(a), Eq(r, c)))
            )
        case Eq(l, IfThenElse(a, b, c)) =>
            iteEliminator(
                OrList(AndList(a, Eq(l, b)), AndList(Not(a), Eq(l, c)))
            )
        case Eq(l, r) => Eq(iteEliminator(l), iteEliminator(r))
        case IfThenElse(a, b, c) => iteEliminator(
            OrList(AndList(a, b), AndList(Not(a), c))
        )
        case _ => term
    }

    var variables: Map[Var, Sort] = Map.empty
    def getVariablesAndToCNF(term: Term): (Term, Map[Var, Sort]) = {
        variables = Map.empty
        val t = getVariables(iteEliminator(term))
        val cnfTerm = cnf(t)
        (cnfTerm, variables)
    }

    /*
        Extract universal quantifiers out, assumes there is no fragment like not(forall ...) (should be transfer to "exist" before)
        eg: forall x:A . (f(x) and (forall y:B . g(x,y)))
        =>  get x->A, y->B, then return f(x) and g(x, y)
     */
    def getVariables(term: Term): Term = term match {
        case Forall(vars, body) => {
            vars.foreach(av => variables = variables + (av.variable -> av.sort))
            getVariables(body)
        }
        case Exists(vars, body) => Errors.Internal.impossibleState("Existential quantifiers should not appear here.")
        case Implication(p, q) => getVariables(OrList(Not(p), q))
        case Iff(p, q) => getVariables(OrList(AndList(p, q), AndList(Not(p), Not(q))))
        case Not(body) => Not(getVariables(body))
        case App(f, args) => App(f, args.map(getVariables))
        case Eq(l, r) => Eq(getVariables(l), getVariables(r))
        case AndList(args) => AndList(args.map(getVariables))
        case OrList(args) => OrList(args.map(getVariables))
        case Top | Bottom | Var(_) | BuiltinApp(_, _) | DomainElement(_, _)
             | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
             | Not(Var(_)) | Not(BuiltinApp(_, _)) => term
        //        case _ => term
    }

    /*
        Returns the conjunctive normal form of a term.
        It is assumed that:
            1. Eq is not used on sort Bool and so uses of Eq are atomic.
            2. applications and arguments to applications are atomic.
            3. there is no existential quantifier in the term ( term should be skolemized before ).
     */
    def cnf(term: Term): Term = term match {
        case Exists(vars, body) => Errors.Internal.impossibleState("Existential quantifiers should not appear here.")
        case Forall(vars, body) => Forall(vars, cnf(body))
        case Implication(p, q) => cnf(OrList(Not(p), q))
        case Iff(p, q) => cnf(OrList(AndList(p, q), AndList(Not(p), Not(q))))
        case Not(body) => body match {
            case Not(body) => cnf(body)
            case App(_, _) | Eq(_, _) | Top | Bottom | Var(_) | BuiltinApp(_, _) | DomainElement(_, _)
                 | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_) => term
            case AndList(arguments) => cnf(OrList(arguments.map(arg => Not(arg))))
            case OrList(arguments) => cnf(AndList(arguments.map(Not)))
        }
        case App(f, args) => App(f, args.map(cnf)) // treat as a variable
        case Eq(l, r) => Eq(cnf(l), cnf(r)) // treat as a variable
        case Top | Bottom | Var(_) | BuiltinApp(_, _) | DomainElement(_, _)
             | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
             | Not(Var(_)) | Not(BuiltinApp(_, _)) => term

        case AndList(args) => {
            var ret: Seq[Term] = Seq.empty
            for (arg <- args) {
                val tmp = cnf(arg)
                tmp match {
                    case AndList(arguments) => ret = ret ++ arguments
                    case OrList(arguments) => ret = ret :+ tmp
                    case App(_, _) | Eq(_, _) | Top | Bottom | Var(_) | BuiltinApp(_, _) | DomainElement(_, _)
                         | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
                         | Not(Var(_)) | Not(BuiltinApp(_, _)) | Not(App(_, _)) | Not(Eq(_, _)) => ret = ret :+ tmp
                    case _ => {
                        println(tmp)
                        Errors.Internal.impossibleState("Bug Point 1")
                    }
                }
            }
            ret = ret.filterNot(r => r == Top)
            if (ret.size > 1) AndList(ret)
            else ret.head
        }

        case OrList(args) => {
            val n = args.size
            var list: Seq[Seq[Term]] = Seq.empty
            for (arg <- args) {
                val tmp = cnf(arg)
                tmp match {
                    case AndList(arguments) => list = list :+ arguments
                    case OrList(arguments) => list = list :+ Seq(tmp)
                    case App(_, _) | Eq(_, _) | Top | Bottom | Var(_) | BuiltinApp(_, _) | DomainElement(_, _)
                         | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
                         | Not(Var(_)) | Not(BuiltinApp(_, _)) | Not(App(_, _)) | Not(Eq(_, _)) => list = list :+ Seq(tmp)
                    case _ => Errors.Internal.impossibleState("Bug Point 2")
                }
            }

            var raw: Seq[Seq[Term]] = list.head.map {
                case OrList(arguments) => arguments
                case t => Seq(t)
            }
            for (i <- 1 until n) raw = mul(raw, list(i))
            var andlist = for (i <- raw) yield {
//                val tmp = i.filterNot(t => t == Bottom)
                val tmp = i
                if (tmp.size > 1) OrList(tmp)
                else tmp.head
            }
            if(andlist.forall(_ == Top)) return Top
            andlist = andlist.filterNot(ad => ad == Top)
//            if(andlist.isEmpty) {
//                println("term: " + term + "is empty")
//            }
            if (andlist.size > 1) AndList(andlist)
            else andlist.head
        }
    }

    def mul(a: Seq[Seq[Term]], b: Seq[Term]): Seq[Seq[Term]] = {
        val m = a.size
        val n = b.size
        var result: Seq[Seq[Term]] = Seq.empty
        for (i <- 0 until m; j <- 0 until n) {
            result = b(j) match {
                case OrList(arguments) => result :+ (a(i) ++ arguments)
                case _ => result :+ (a(i) :+ b(j))
            }
        }
        result
    }
}