package fortress.operations

import scala.language.implicitConversions
import fortress.msfol._
import fortress.util.Errors

trait SortSubstitution {
    
    def apply(sort: Sort): Sort
    
    def apply(term: Term): Term = term match {
        case Top | Bottom | Var(_)  => term
        case Not(p) => Not(apply(term))
        case AndList(args) => AndList(args map apply)
        case OrList(args) => OrList(args map apply)
        case Distinct(args) => Distinct(args map apply)
        case Implication(p, q) => Implication(apply(p), apply(q))
        case Iff(p, q) => Iff(apply(p), apply(q))
        case Eq(l, r) => Eq(apply(l), apply(r))
        case App(name, args) => App(name, args map apply)
        case Exists(avars, body) => {
            val newVars = avars map {avar => Var(avar.name) of apply(avar.sort)}
            Exists(newVars, apply(body))
        }
        case Forall(avars, body) => {
            val newVars = avars map {avar => Var(avar.name) of apply(avar.sort)}
            Forall(newVars, apply(body))
        }
        case EnumValue(_) | DomainElement(_, _) | BuiltinApp(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => ???
    }
    
    def apply(f: FuncDecl): FuncDecl = f match {
        case FuncDecl(name, argSorts, resultSort) => FuncDecl(name, argSorts map apply, apply(resultSort))
    }
    
    def apply(avar: AnnotatedVar): AnnotatedVar = avar match {
        case AnnotatedVar(name, sort) => AnnotatedVar(name, apply(sort))
    }
    
    def apply(signature: Signature): Signature = signature match {
        case Signature(sorts, functionDeclarations, constants, enumConstants) => {
            Errors.precondition(enumConstants.isEmpty)
            Signature(
                sorts map apply,
                functionDeclarations map apply,
                constants map apply,
                Map.empty
            )
        }
    }
    
}

object SortSubstitution {
    // Because of type erasure we can't extend both Function[Sort, Sort] and Function[Term, Term]
    // so we use delegation and implicits to simulate this
    
    implicit def asSortFunction(sigma: SortSubstitution): Sort => Sort = (sort => sigma(sort))
    
    implicit def asTermFunction(sigma: SortSubstitution): Term => Term = (term => sigma(term))
}
