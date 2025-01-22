package fortress.operations

import fortress.data._
import fortress.msfol._
import fortress.util.Errors

object QuantifiersToDefinitions {

    case class Result(resultTerm: Term, definitions: Set[FunctionDefinition])

    def apply(term: Term, sig: Signature, nameGen: NameGenerator, contextIn: Option[Context] = None): Result = {
        val definitions = scala.collection.mutable.Set[FunctionDefinition]()
        var context = contextIn match {
            case Some(ctx) => ctx
            case None => Context.empty(sig)
        }

        def performHoist(body: Term): Term = {
            val (call, defn) = DefinitionHoister(body, context, Sort.Bool, nameGen)
            definitions.add(defn)
            call
        }

        def recur(term: Term): Term = term match {
            case Top | Bottom | Var(_) | DomainElement(_, _) | IntegerLiteral(_)
                 | BitVectorLiteral(_, _) | EnumValue(_) | SetCardinality(_) => term
            case Not(p) => Not(recur(p))
            case AndList(args) => AndList(args map recur)
            case OrList(args) => OrList(args map recur)
            case Distinct(args) => Distinct(args map recur)
            case Iff(left, right) => Iff(recur(left), recur(right))
            case Implication(left, right) => Implication(recur(left), recur(right))
            case Eq(left, right) => Eq(recur(left), recur(right))
            case App(fn, args) => App(fn, args map recur)
            case BuiltinApp(fn, args) => BuiltinApp(fn, args map recur)
            case IfThenElse(c, t, f) => IfThenElse(recur(c), recur(t), recur(f))
            case Forall(vars, body) => {
                context = context.stackPush(vars)
                // recur first so that we translate bottom-up
                val result = performHoist(recur(body))
                context = context.stackPop(vars.size)
                Forall(vars, result)
            }
            case Exists(vars, body) => {
                context = context.stackPush(vars)
                // recur first so that we translate bottom-up
                val result = performHoist(recur(body))
                context = context.stackPop(vars.size)
                Exists(vars, result)
            }
            case _ => Errors.Internal.impossibleState(
                s"QuantifiersToDefinitions not implemented on $term (hint: are closures eliminated?)")
        }

        val reduced = recur(term)
        Result(reduced, definitions.toSet)
    }

}
