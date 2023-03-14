package fortress.transformers

import fortress.msfol._
import fortress.problemstate._

object ZeroArityApplicationTransformer extends ProblemStateTransformer {
    val name = "ZeroArityApplicationTransformer"

    def getZeroArityDecls(problemState: ProblemState): Set[String] = {
        val decls = problemState.theory.signature.functionDeclarations

        decls.collect({case FuncDecl(name, args, _) if args.isEmpty => name})
    }

    def getZeroArityDefns(problemState: ProblemState): Set[String] = {
        val defns = problemState.theory.signature.functionDefinitions
        
        defns.collect({case FunctionDefinition(name, args, _, _) if args.isEmpty => name})
    }

    def recur(term: Term, zeroArityFunctions: Set[String]): Term = term match {
        case Var(x) if zeroArityFunctions contains x => App(x)
        case Exists(vars, body) => {
            val newZeroArity = zeroArityFunctions diff vars.map(_.name).toSet
            val newBody = recur(body, newZeroArity)
            Exists(vars, newBody)
        }
        case Forall(vars, body) => {
            val newZeroArity = zeroArityFunctions diff vars.map(_.name).toSet
            val newBody = recur(body, newZeroArity)
            Forall(vars, newBody)
        }
        case IfThenElse(condition, ifTrue, ifFalse) => {
            IfThenElse(
                recur(condition, zeroArityFunctions),
                recur(ifTrue, zeroArityFunctions),
                recur(ifFalse, zeroArityFunctions)
            )
        }
        case imp: Implication => imp.mapArguments(recur(_, zeroArityFunctions))
        case Not(body) => Not(recur(body, zeroArityFunctions))
        case Iff(left, right) => Iff(recur(left, zeroArityFunctions), recur(right, zeroArityFunctions))
        case dist: Distinct => dist.mapArguments(recur(_, zeroArityFunctions))
        case eq: Eq => eq.mapArguments(recur(_, zeroArityFunctions))
        case c: Closure => c.mapArguments(recur(_, zeroArityFunctions))
        case rc: ReflexiveClosure => rc.mapArguments(recur(_, zeroArityFunctions))
        case conjunction: AndList => conjunction.mapArguments(recur(_, zeroArityFunctions))
        case disjunction: OrList => disjunction.mapArguments(recur(_, zeroArityFunctions))
        case app: App => app.mapArguments(recur(_, zeroArityFunctions))
        case lt: LeafTerm => lt
        case bia: BuiltinApp => bia.mapArguments(recur(_, zeroArityFunctions))
    }

    def apply(problemState: ProblemState): ProblemState = {
        // get the names of all the zero-arity functions
        val zeroArityFunctions = getZeroArityDecls(problemState) union getZeroArityDefns(problemState)

        val newAxioms = problemState.theory.axioms.map(recur(_, zeroArityFunctions))
        val newTheory = Theory(problemState.theory.signature, newAxioms)
        problemState.withTheory(newTheory)
    }
}