package fortress.operations

import fortress.data._
import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors

/**
  * Given a term, hoist the term into a definition, with the parameters of the definition
  * being the free variables. Return a term representing a call to the definition and the
  * definition itself.
  */
object DefinitionHoister {

    // context must map every free variable in term to its sort
    // termSort must be the sort that term resolves to
    // This are necessary because we don't store the sorts in the AST.
    def apply(term: Term, context: Context, termSort: Sort, nameGen: NameGenerator): (Term, FunctionDefinition) = {
        val freeVars = term.freeVars(context.signature).toSeq
        val annotatedFreeVars = freeVars.map { freeVar =>
            val sort = context.lookupSort(freeVar)
            Errors.Internal.precondition(sort.nonEmpty,
                s"Free variable $freeVar was not passed a sort in DefinitionHoister")
            AnnotatedVar(freeVar, sort.get)
        }
        val name = nameGen.freshName("__@Hoist")
        val defn = FunctionDefinition(name, annotatedFreeVars, termSort, term)

        (App(defn.name, freeVars), defn)
    }

}
