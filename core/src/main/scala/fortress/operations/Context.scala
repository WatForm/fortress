package fortress.operations

import fortress.msfol._
import fortress.util.Errors
// Immutable
class Context(val signature: Signature, variableStack: List[AnnotatedVar]) {
    def stackPush(avars: Seq[AnnotatedVar]): Context = {
        // Note that variables are pushed in order, so the last variable in the list becomes the top of the stack
        var newStack = variableStack
        for(av <- avars) {
            newStack = av :: newStack
        }
        new Context(signature, newStack)
    }

    def stackPop(numItems: Int): Context = {
        var newStack = variableStack
        for(i <- 1 to numItems) {
            newStack = newStack.tail
        }
        new Context(signature, newStack)
    }

    def lookupSort(variable: Var): Option[Sort] = {
        // Check if it is in the Context
        // Note that the context is used as a stack, so we just need to iterate
        // from front to back and not have to worry about shadowed variables.
        // e.g. in (forall v: A, forall v : B, p(v)), the context will look like
        // List[v: B, v: A], and the term will fail to typecheck if p : A -> Bool
        // since the use of v will have type B
        mostRecentStackAppearence(variable)
        // If it is not in the stack, check if is in the declared constants
            .orElse(signature.getAnnotatedVarOfConstant(variable))
            // Gives Option[AnnotatedVar], take sort
            .map(_.sort)
    }

    def mostRecentStackAppearence(variable: Var): Option[AnnotatedVar] = variableStack.find(_.name == variable.name)

    def updateSignature(newSignature: Signature): Context = new Context(newSignature, variableStack)
}

object Context {
    def empty(signature: Signature): Context = new Context(signature, List.empty)
}