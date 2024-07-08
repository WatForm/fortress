package fortress.transformers

import fortress.msfol._
import fortress.operations._
import fortress.problemstate._
import fortress.interpretation._
import fortress.operations.TheoryOps._
import fortress.operations.IntegerPredicateFinder._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator

object AxiomatizeIntPredDefinitionsTransformer extends ProblemStateTransformer {
  
    def apply(problemState: ProblemState): ProblemState = {
        val theory = problemState.theory
        val oldSig = theory.signature
        val oldFuncDefs = oldSig.functionDefinitions

        val integerPredicates = theory.intAndBitvectorPredicates

        // Check if an annotated variable is of an integer type
        def isIntAvar(avar: AnnotatedVar): Boolean = avar.sort match {
            case IntSort | BitVectorSort(_) => true
            case _ => false
        }
        // get the variables which are integer typed from a set of avars
        def getIntVars(avars: Set[AnnotatedVar]): Set[Var] = {
            avars.withFilter(isIntAvar).map(_.variable)
        }

        val intConstants = getIntVars(theory.constantDeclarations) union getIntVars(theory.constantDefinitions.map(_.avar))

        val functionsToTransform: Set[FunctionDefinition] = oldFuncDefs.filter({case FunctionDefinition(_, argSortedVar, _, body) =>
            val intArgs = getIntVars(argSortedVar.toSet)
            val allIntVars = intConstants 
            containsIntegerPredicate(body, allIntVars, integerPredicates)
        })

        // axiomatize each of the functions
        val newFuncDecls: Seq[FuncDecl] = functionsToTransform.toSeq.map({case FunctionDefinition(name, args, resultSort, _) =>
             FuncDecl(name, args.map(_.sort), resultSort)
            })
        
        
        val funcAxioms: Seq[Term] = functionsToTransform.toSeq.map(fDef => {
            // forall args. f(args) = body
            Forall(fDef.argSortedVar, Eq(App(fDef.name, fDef.argSortedVar.map(_.variable)), fDef.body))
        })

        
        val newTheory = theory.withoutFunctionDefinitions(functionsToTransform)
        .withFunctionDeclarations(newFuncDecls)
        .withAxioms(funcAxioms)

        problemState.copy(
            theory = newTheory
        )
    }
    override def name: String = "Axiomatize Integer-Predicate Definitions Transformer"
}
