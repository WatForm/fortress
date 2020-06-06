package fortress.operations

import fortress.msfol._
import fortress.data._
import scala.language.implicitConversions

case class TermOps private (term: Term) {
    /** Given a signature, typechecks the term with respect to the signature.
      * Returns a TypeCheckResult containing the sort of the term, AND a new term
      * that is equal to the old term but with instances of Eq replaced with Iff
      * when comparing Bool sorts. Such a term is called "sanitized".
      */
    def typeCheck(signature: Signature): TypeCheckResult = (new TypeChecker(signature)).visit(term)
    
    /** Returns the set of Vars that appear unquantified in this term.
      * This only looks at syntax without respect to a given signature,
      * so it could also include what are intended to be constants.
      */ 
    def freeVarConstSymbols: Set[Var] = RecursiveAccumulator.freeVariablesIn(term)
    
    /** Returns the set of free variables of this term with respect
      * to the given signature. Constants of the signature are not included.
      */ 
    def freeVars(signature: Signature): Set[Var] = {
        val constants = signature.constants.map(_.variable)
        RecursiveAccumulator.freeVariablesIn(term) diff constants
    }
    
    /** Returns the negation normal form version of this term.
      * The term must be sanitized to call this method.
      */
    def nnf: Term = TermConverter.nnf(term)
    
    /** Does not account for variable capture.
      * If in doubt do not use this function.
      */
    def fastSubstitute(substitutions: Map[Var, Term]): Term =
        FastSubstituter(substitutions, term)
    
    def substitute(toSub: Var, subWith: Term, nameGenerator: NameGenerator): Term =
        Substituter(toSub, subWith, term, nameGenerator)
    
    def substitute(toSub: Var, subWith: Term): Term =
                substitute(toSub, subWith, new IntSuffixNameGenerator(Set.empty[String], 0))
    
    /** Returns a term that is alpha-equivalent to this one but whose quantified
      * variables are instead De Bruijn indices. Note that these indices are prefixed
      * by an underscore to make it clearer (e.g. the first quantified variable is "_1")
      */
    def deBruijn: Term = new DeBruijnConverter().convert(term)
    
    /** Returns true iff the other term is alpha-equivalent to this term. */
    def alphaEquivalent(other: Term): Boolean = deBruijn == TermOps(other).deBruijn
    
    def expandQuantifiers(sortInstantiations: Map[Sort, Seq[Term]]): Term =
        QuantifierExpander(term, sortInstantiations)
        
    def expandQuantifiersAndSimplify(sortInstantiations: Map[Sort, Seq[Term]]): Term =
        QuantifierExpanderSimplifier(term, sortInstantiations)
    
    def simplify: Term = Simplifier.simplify(term)
    
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
    
    def equalsOneOf(terms: Seq[Term]): Term = Or.smart(terms map (term === _))
    
    def equalsOneOfFlip(terms: Seq[Term]): Term = Or.smart(terms map (_ === term))
    
    def smtlib: String = {
        val writer = new java.io.StringWriter
        SmtlibConverter.write(term, writer)
        writer.toString
    }
    
    def smtlibAssertion: String = {
        val writer = new java.io.StringWriter
        writer.write("(assert ")
        SmtlibConverter.write(term, writer)
        writer.write(')')
        writer.toString
    }
}

object TermOps {
    implicit def wrapTerm(term: Term): TermOps = TermOps(term)
}
