package fortress.transformers.Integers

import fortress.transformers.ProblemStateTransformer
import fortress.msfol._
import fortress.transformers.Polarity
import fortress.problemstate.ProblemState

abstract class PermissiveTransformer extends ProblemStateTransformer {

    def apply(problemState: ProblemState): ProblemState = {
        val oldTheory = problemState.theory
        val sig = oldTheory.signature
        val newAxioms: Set[Term] = oldTheory.axioms.map(permissive(_, sig, Polarity.Positive))
        val newTheory = oldTheory.copy(axioms = newAxioms)
        
        // No need to unapply, we haven't changed anything
        problemState.withTheory(newTheory)
    }


    // Applies permissive transformation to an axiom
    def permissive(axiom: Term, sig: Signature, pol: Polarity.Polarity): Term = {
        val (transformed, unknown) = unknownCheck(axiom, sig, pol)  
        unknown match {
            case Bottom => transformed
            case _ => And(transformed, Not(unknown))
        }
    }

    // overrides for unknown checks
    // Given a term, return a function that takes the unknown checks for its argumnents and returns
    // the new term and an unknown check for the term
    var overrides: PartialFunction[Term, (Term, Term)]
    // canOverflow takes a term and the unknown checks for each of its arguments
    // it returns the new term and an unknown check for the term
    def unknownCheck(term: Term, sig: Signature, pol: Polarity.Polarity): (Term, Term) = {
        if (overrides isDefinedAt term) {
            overrides(term)
        } else term match {
            case AndList(arguments) => {
                val results = arguments.map(unknownCheck(_, sig, pol))

                // Argument is known false if it is not true and not unknown
                val knownFalse = results.map({case (arg, unknown) => And(Not(arg), Not(unknown))})

                val (newArgs, unknowns) = results.unzip

                val newTerm = AndList(newArgs)
                val unknown = And(
                    OrList(unknowns), // Some value is unknown
                    Not(OrList(knownFalse)), // no value is known to be false
                )
                // TODO shortcut if polarity is known
                (newTerm, unknown)
            }
            case OrList(arguments) => {
                val results = arguments.map(unknownCheck(_, sig, pol))

                // Argument is known true if it true and not unknown
                val knownTrue = results.map({case (arg, unknown) => And(arg, Not(unknown))})

                val (newArgs, unknowns) = results.unzip

                val newTerm = OrList(newArgs)
                val unknown = And(
                    OrList(unknowns), // Some value is unknown
                    Not(OrList(knownTrue)), // no value is known to be false
                )

                // TODO shortcut if polarity is known
                (newTerm, unknown)
            }

            case Not(arg) => {
                val (newArg, unknown) = unknownCheck(arg, sig, Polarity.flip(pol))

                (Not(newArg), unknown)
            }

            case Exists(vars, body) => {
                val (newBody, unknownBody) = unknownCheck(body, sig, pol)

                // Ignore invalid values
                val newTerm = Exists(vars, And(newBody, Not(unknownBody)))
                // Unkown if everything is unknown
                val unknown = Forall(vars, unknownBody)
                

                (newTerm, unknown)
            }

            case Forall(vars, body) => {
                val (newBody, unknownBody) = unknownCheck(body, sig, pol)
                // Ignore invalid values
                val newTerm = Forall(vars, Or(newBody, unknownBody))
                // Unkown if everything is unknown
                val unknown = Forall(vars, unknownBody)
                (newTerm, unknown)
            }

            // Leaf term does not overflow
            case (_: LeafTerm) => {
                (term, Bottom)
            }

            case Iff(left, right) => {
                val (newLeft, unknownLeft) = unknownCheck(left, sig, Polarity.Indeterminate)
                val (newRight, unknownRight) = unknownCheck(right, sig, Polarity.Indeterminate)

                val newTerm = Iff(newLeft, newRight)
                val unknown = Or(unknownLeft, unknownRight)
                (newTerm, unknown)
            }

            case Implication(left, right) => {
                val transformed = Or(Not(left), right)
                unknownCheck(transformed, sig, pol)
            }

            case Eq(left, right) => {
                // TODO double check that this cannot be for booleans
                val (newLeft, unknownLeft) = unknownCheck(left, sig, Polarity.Indeterminate)
                val (newRight, unknownRight) = unknownCheck(right, sig, Polarity.Indeterminate)

                val newTerm = Iff(newLeft, newRight)
                val unknown = Or(unknownLeft, unknownRight)
                (newTerm, unknown)
            }

            case Distinct(args) => {
                // TODO check distinct is not on booleans
                // TODO is there a better way to "distinct on only known values?"
                // Skipping for now
                val results = args.map(unknownCheck(_, sig, Polarity.Indeterminate))

                // unknown if anything is unknown
                val (newTerms, unknowns) = results.unzip
                val newTerm = Distinct(newTerms)
                val unknown = OrList(unknowns)
                (newTerm, unknown)
            }

            case IfThenElse(condition, ifTrue, ifFalse) => {
                val (newCond, unknownCond) = unknownCheck(condition, sig, Polarity.Indeterminate)
                val (newTrue, unknownTrue) = unknownCheck(ifTrue, sig, pol)
                val (newFalse, unknownFalse) = unknownCheck(ifFalse, sig, pol)

                // unknown if condition is unknown or branch taken is unknown
                val unknown = Or(
                    unknownCond,
                    And(newCond, unknownTrue),
                    And(Not(newCond), unknownFalse),
                )
                val newITE = IfThenElse(newCond, newTrue, newFalse)

                (newITE, unknown)
            }

            case Closure(functionName, arg1, arg2, fixedArgs) => {
                val (newArg1, unknown1) = unknownCheck(arg1, sig, Polarity.Indeterminate)
                val (newArg2, unknown2) = unknownCheck(arg2, sig, Polarity.Indeterminate)
                val (newFixed, fixedUnknowns) = fixedArgs.map(unknownCheck(_, sig, Polarity.Indeterminate)).unzip

                val newTerm = Closure(functionName, newArg1, newArg2, newFixed)
                // Unknown if any input is unknown
                val unknown = OrList(unknown1 +: unknown2 +: fixedUnknowns)
                (newTerm, unknown)
            }

            case ReflexiveClosure(functionName, arg1, arg2, fixedArgs) => {
                val (newArg1, unknown1) = unknownCheck(arg1, sig, Polarity.Indeterminate)
                val (newArg2, unknown2) = unknownCheck(arg2, sig, Polarity.Indeterminate)
                val (newFixed, fixedUnknowns) = fixedArgs.map(unknownCheck(_, sig, Polarity.Indeterminate)).unzip

                val newTerm = ReflexiveClosure(functionName, newArg1, newArg2, newFixed)
                // Unknown if any input is unknown
                val unknown = OrList(unknown1 +: unknown2 +: fixedUnknowns)
                
                (newTerm, unknown)
            }


            // TODO
            // If we are doing bitvectors, the override should catch this?
            // Or do we include it here and not have an override for opfi?
            case BuiltinApp(function, arguments) => {
                val (newArgs, unknowns) = arguments.map(unknownCheck(_, sig, Polarity.Indeterminate)).unzip

                val newTerm = BuiltinApp(function, newArgs)
                val unknown = OrList(unknowns)
                (newTerm, unknown)
            }

            // TODO function definitions?
            case App(fname, args) => {
                // TODO check if predicate for polarity simplification

                val (newArgs, unknowns) = args.map(unknownCheck(_, sig, Polarity.Indeterminate)).unzip
                val newTerm = App(fname, newArgs)
                val unknown = OrList(args)
                (newTerm, unknown)
            }


            case Exists2ndOrder(declarations, body) => ???
            case Forall2ndOrder(declarations, body) => ???

        }
    }

    

}