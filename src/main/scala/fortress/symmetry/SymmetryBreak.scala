package fortress.symmetry

import fortress.msfol._
import fortress.util.Errors

object Symmetry {
    def smartOr(terms: Seq[Term]): Term = {
        Errors.precondition(terms.nonEmpty)
        if(terms.size == 1) terms.head
        else OrList(terms)
    }
    
    def csConstantEqualities(sort: Sort, constants: IndexedSeq[AnnotatedVar],
        unusedValues: IndexedSeq[DomainElement], usedValues: IndexedSeq[DomainElement]): Set[Term] = {
        Errors.precondition(!sort.isBuiltin)
        Errors.precondition(constants.forall(_.sort == sort))
        Errors.precondition(unusedValues.forall(_.sort == sort))
        Errors.precondition(unusedValues.forall(_.sort == sort))
        Errors.precondition((unusedValues intersect usedValues).isEmpty)
        
        val n = constants.size
        val m = unusedValues.size
        val r = scala.math.min(n, m)
        
        val equalityConstraints = for {
            k <- 0 to (r - 1) // Enumerate constants
        } yield {
            val possibleUnusedEqualities: Seq[Term] = for {
                i <- 0 to k // Enumerate unused values
            } yield {constants(k).variable === unusedValues(i)}
            
            val possibleUsedEqualities: Seq[Term] = for {
                v <- usedValues
            } yield {constants(k).variable === v}
            
            val possibleEqualities: Seq[Term] = possibleUsedEqualities ++ possibleUnusedEqualities
            
            smartOr(possibleEqualities)
        }
        
        equalityConstraints.toSet
    }
    
    def csConstantImplications(sort: Sort, constants: IndexedSeq[AnnotatedVar],
        unusedValues: IndexedSeq[DomainElement], usedValues: IndexedSeq[DomainElement]): Set[Term] = {
        Errors.precondition(!sort.isBuiltin)
        Errors.precondition(constants.forall(_.sort == sort))
        Errors.precondition(unusedValues.forall(_.sort == sort))
        Errors.precondition(unusedValues.forall(_.sort == sort))
        Errors.precondition((unusedValues intersect usedValues).isEmpty)
        
        val n = constants.size
        val m = unusedValues.size
        val r = scala.math.min(n, m)
        
        val implications = for(
            k <- 1 to (r - 1); // Enumerates constants
            d <- 1 to k // Enumerates values
        ) yield {
            val possibleEqualities = for {
                i <- 0 to k - 1
            } yield {constants(i).variable === unusedValues(d - 1)}
            
            Implication(
                constants(k).variable === unusedValues(d),
                smartOr(possibleEqualities)
            )
        }
        
        implications.toSet
    }
}
