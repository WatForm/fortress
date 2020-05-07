package fortress.operations

import fortress.msfol._
import fortress.data._
import scala.language.implicitConversions

case class TermOps(term: Term) {
    /** Returns the set of Vars that appear unquantified in this term.
      * This only looks at syntax without respect to a given signature,
      * so it could also include what are intended to be constants.
      */ 
    def freeVarConstSymbols: Set[Var] = RecursiveAccumulator.freeVariablesIn(term)
    
    /** Returns the negation normal form version of this term.
      * The term must be sanitized to call this method.
      */
    def nnf: Term = TermConverter.nnf(term)
    
    /** Does not account for variable capture.
      * If in doubt do not use this function.
      */
    def recklessSubstitute(substitutions: Map[Var, Term]): Term =
        RecklessSubstituter(substitutions, term)
    
    def recklessUnivInstantiate(sortInstantiations: Map[Sort, Seq[Term]]): Term =
        RecklessUnivInstantiator(term, sortInstantiations)
    
    def simplify: Term = TermConverter.simplify(term)
    
    def eliminateDomainElements: Term = DomainElementEliminator(term)
    
    def eliminateEnumValues(eliminationMapping: Map[EnumValue, DomainElement]): Term = EnumValueEliminator(eliminationMapping)(term)
    
    def allEnumValues: Set[EnumValue] = RecursiveAccumulator.enumValuesIn(term)
    
    def finitizeIntegers(bitwidth: Int): Term = TermConverter.intToSignedBitVector(term, bitwidth)
    
    /** Returns the set of all symbol names used in the term, including:
      * free variables and constants, bound variables (even those that aren't used),
      * function names, and sort names that appear on variable bindings.
      */
    def allSymbols: Set[String] = RecursiveAccumulator.allSymbolsIn(term)
    
    /** Returns the set of all domain elements occuring within the term. */
    def domainElements: Set[DomainElement] = RecursiveAccumulator.domainElementsIn(term)
}

object TermOps {
    implicit def wrapTerm(term: Term): TermOps = TermOps(term)
}
