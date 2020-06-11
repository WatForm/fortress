package fortress.operations

import fortress.msfol._
import fortress.data.CartesianSeqProduct
import fortress.util.Errors
import fortress.operations.TermOps._

// TODO can we make this faster?

/* The instantiator will NOT avoid variable capture; it is the responsibility
* of the caller to make sure the instantiation terms do not contain free
* variables that could be captured.
* For example, it would be okay to instantiate with domain elements or fresh
* constants that do not share the same name as any quantified variable.
*/
object QuantifierExpander {
    
    def apply(term: Term, sortInstantiations: Map[Sort, Seq[Term]]): Term = {
        def instantiate(t: Term): Term = t match {
            case Top | Bottom | Var(_) | DomainElement(_, _) | IntegerLiteral(_)
                | BitVectorLiteral(_, _) | EnumValue(_) => t
            case Not(arg) => Not(instantiate(arg))
            case AndList(args) => AndList(args map instantiate)
            case OrList(args) => OrList(args map instantiate)
            case Distinct(args) => Distinct(args map instantiate)
            case Implication(left, right) => Implication(instantiate(left), instantiate(right))
            case Iff(left, right) => Iff(instantiate(left), instantiate(right))
            // We assume eq, app do not contain quantifiers, so we do not need to go further
            // If we change the implementation from just using direct substitution, we will need to change this
            case Eq(_, _) | App(_, _) | BuiltinApp(_, _) => t 
            case Forall(annotatedVars, body) => {
                // Reorder by whether can instantiate and then call helper function
                val (doNotInstantiate, toInstantiate) = annotatedVars.partition(_.sort.isBuiltin)
                if (doNotInstantiate.isEmpty) And.smart(simpleQuantifiers(annotatedVars, body))
                else Forall(doNotInstantiate, And.smart(simpleQuantifiers(toInstantiate, body)))
            }
            case Exists(annotatedVars, body) => {
                // Reorder by whether can instantiate and then call helper function
                val (doNotInstantiate, toInstantiate) = annotatedVars.partition(_.sort.isBuiltin)
                if (doNotInstantiate.isEmpty) Or.smart(simpleQuantifiers(annotatedVars, body))
                else Exists(doNotInstantiate, Or.smart(simpleQuantifiers(toInstantiate, body)))
            }
        }
            
        def simpleQuantifiers(annotatedVars: Seq[AnnotatedVar], body: Term): Seq[Term] = {
            // TODO this assumes each sort is instantiated, which we may change later
            // TODO does the order of quantifier instantiation matter? Here we do a bottom up approach
            
            val instantiatedBody: Term = instantiate(body)
            // Forall x_1: A_1, x_2 : A_2, ... x_n: A_n
            // Where A_i is to be instantiated using the set S_i
            // Get the list [S_1, S_2, ..., S_n]
            // and the list [x_1, x_2, ..., x_n]
            val listOfSortSets = new scala.collection.mutable.ListBuffer[IndexedSeq[Term]]
            for(av <- annotatedVars) {
                val sort = av.sort
                listOfSortSets += sortInstantiations(sort).toIndexedSeq
            }
            val vars = annotatedVars map (_.variable)
            
            val cartesianProduct = (new CartesianSeqProduct[Term](listOfSortSets.toIndexedSeq)).toSeq
            val instantiatedVersions: Seq[Term] = cartesianProduct map { substitution: Seq[Term] => {
                Errors.verify(substitution.size == vars.size)
                
                val varSubstitutions: Map[Var, Term] = (vars zip substitution).toMap

                // NOTE because we are substituting with fresh variables, there
                // should never be any variable capture or any other name issues
                instantiatedBody.fastSubstitute(varSubstitutions.toMap)
            }}
            instantiatedVersions
        }
        
        instantiate(term)
    }
}
