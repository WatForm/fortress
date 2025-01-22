package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.operations.TermOps._
import java.lang.IllegalArgumentException
import fortress.util.Errors

// Skolemizes a given term, which must be in negation normal form.
// Free variables in the given term are ignored, so the top level term must be
// closed with respect to the signature in question for this operation to be valid.

object Skolemization {

    case class SkolemResult(skolemizedTerm: Term, skolemConstants: Set[AnnotatedVar], skolemFunctions: Set[FuncDecl])
    
    // Mutates the name generator
    def skolemize(axiom: Term, sig: Signature, nameGen: NameGenerator): SkolemResult = {
        val skolemFunctions = scala.collection.mutable.Set[FuncDecl]()
        val skolemConstants = scala.collection.mutable.Set[AnnotatedVar]()
        var context = Context.empty(sig)

        def recur(term: Term): Term = term match {
            case Top | Bottom | Var(_) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) | EnumValue(_) => term
            case Not(p) => Not(recur(p))
            case AndList(args) => AndList(args map recur)
            case OrList(args) => OrList(args map recur)
            case Distinct(_) | Iff (_, _) | Implication(_, _) => Errors.Internal.preconditionFailed(s"Term not in negation normal form: ${term}")


            // Arguments to fcn/builtinapp with unknown polarity cannot be skolemized
            case Eq(l, r) => term
            case App(fn, args) => term
            case BuiltinApp(fn, args) => term
            case IfThenElse(c, t, f) => term
            case SetCardinality(p) => term

            case Forall(avars, body) => {
                context = context.stackPush(avars)
                val r = Forall(avars, recur(body))
                context = context.stackPop(avars.size)
                r
            }
            case Exists(avars, body) => {
                var temporaryBody = body
                for(av <- avars) {
                    // To determine what arguments the skolem function needs, look at the
                    // free variables of (Exists x body), and see which of them are universally 
                    // quantified earlier (which also means we discard constants, unless they are shadowed)
                    // Note that since we remove existential quantifiers from the top down,
                    // any variable on the stack is universally quantified
                    val skolemArguments: Seq[AnnotatedVar] = for {
                        variable <- term.freeVarConstSymbols.toList
                        annotatedVar <- context.mostRecentStackAppearence(variable)
                    } yield annotatedVar

                    // Errors.Internal.assertion(skolemArguments.map(_.variable).toSet == term.freeVars(signature))

                    if(skolemArguments.size == 0) {
                        // Skolem constant
                        val skolemConstantName = nameGen.freshName("sk")
                        
                        val skolemConstant = Var(skolemConstantName) of av.sort
                        skolemConstants += skolemConstant
                        
                        temporaryBody = temporaryBody.substitute(av.variable, skolemConstant.variable)
                        
                        // We also have to update the signature with the new skolem constant
                        // since it might now appear deeper in the new term
                        context = context.updateSignature(context.signature.withConstantDeclaration(skolemConstant))
                    } else {
                        // Skolem function
                        val skolemFunctionName = nameGen.freshName("sk")
                        val argumentSorts = skolemArguments.map(_.sort)
                        val arguments = skolemArguments.map(_.variable)
                        
                        val skolemFunction = FuncDecl(skolemFunctionName, argumentSorts, av.sort)
                        skolemFunctions += skolemFunction
                        
                        val skolemApplication = App(skolemFunctionName, arguments)
                        temporaryBody = temporaryBody.substitute(av.variable, skolemApplication, nameGen)
                        
                        context = context.updateSignature(context.signature.withFunctionDeclaration(skolemFunction))
                    }
                }
                recur(temporaryBody)
            }
            // Arguments with unknown polarity cannot be skolemized
            case Closure(functionName, arg1, arg2, fixedArgs) => term
            case ReflexiveClosure(functionName, arg1, arg2, fixedArgs) => term
        }

        val skolemTerm = recur(axiom)
        SkolemResult(skolemTerm, skolemConstants.toSet, skolemFunctions.toSet)
    }
}