package fortress.msfol

import fortress.util.Errors

object NegationNormalizer {
    def apply(term: Term): Term = {
        // We assume = is between non-Booleans and so is atomic
        // We also assume applications and arguments to applications are atomic
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
            case Top | Bottom | Var(_) | App(_, _) | Eq(_, _) | DomainElement(_, _)
                | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_)
                | Not(Var(_)) | Not(App(_, _)) | Not(Eq(_, _)) => term
            case Not(DomainElement(_, _)) | Not(IntegerLiteral(_))
                |  Not(BitVectorLiteral(_, _)) | Not(EnumValue(_)) => ???
        }
        nnf(term)
    }
}
