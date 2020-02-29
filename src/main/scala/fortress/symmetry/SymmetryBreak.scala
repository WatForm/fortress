package fortress.symmetry

import fortress.msfol._
import fortress.util.Errors

object Symmetry {
    def smartOr(terms: Seq[Term]): Term = {
        Errors.precondition(terms.nonEmpty)
        if(terms.size == 1) terms.head
        else OrList(terms)
    }
    
    def csConstantEqualities(sort: Sort, constants: IndexedSeq[AnnotatedVar], scope: Int,
        usedValues: IndexedSeq[DomainElement]): Set[Term] = {
        Errors.precondition(!sort.isBuiltin)
        Errors.precondition(constants.forall(_.sort == sort))
        Errors.precondition(usedValues.forall(_.sort == sort))
        Errors.precondition(usedValues.forall(_.index <= scope))
        Errors.precondition(usedValues.size < scope)
        
        val unusedValues = (for(i <- 1 to scope) yield DomainElement(i, sort)) diff usedValues
        
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
    
    def csConstantImplications(sort: Sort, constants: IndexedSeq[AnnotatedVar], scope: Int,
        usedValues: IndexedSeq[DomainElement]): Set[Term] = {
        Errors.precondition(!sort.isBuiltin)
        Errors.precondition(constants.forall(_.sort == sort))
        Errors.precondition(usedValues.forall(_.sort == sort))
        Errors.precondition(usedValues.forall(_.index <= scope))
        Errors.precondition(usedValues.size < scope)
        
        val unusedValues = (for(i <- 1 to scope) yield DomainElement(i, sort)) diff usedValues
        
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
    
    def drdFunctionEqualities(f: FuncDecl, scopes: Map[Sort, Int],
        usedResultValues: IndexedSeq[DomainElement]): Set[Term]= {
        Errors.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.precondition(!f.resultSort.isBuiltin)
        Errors.precondition(usedResultValues.forall(_.sort == f.resultSort))
        Errors.precondition(usedResultValues.forall(_.index <= scopes(f.resultSort)))
        Errors.precondition(usedResultValues.size < scopes(f.resultSort))
        
        val unusedResultValues: IndexedSeq[DomainElement] = (for(i <- 1 to scopes(f.resultSort)) yield DomainElement(i, f.resultSort)) diff usedResultValues
        
        val argumentLists = new fortress.util.ArgumentListGenerator(scopes).allArgumentListsOfFunction(f)
        // For the sake of efficiency, the argument list generator does not generate arguments
        // until they are needed
        // Therefore we don't know how many argument tuples there are yet, and have to generate the constraints
        // imperatively rather than functionally
        val constraints = new scala.collection.mutable.ListBuffer[Term]
        var k = 0
        val argListIterator = argumentLists.iterator
        while(k < unusedResultValues.size && argListIterator.hasNext) {
            val argList = argListIterator.next
            
            val app = App(f.name, argList)
            val possibleUsedEqualities =
                for(v <- usedResultValues) yield {app === v}
            val possibleUnusedEqualities =
                for(i <- 0 to k) yield {app === unusedResultValues(i)}
            val possibleEqualities = possibleUsedEqualities ++ possibleUnusedEqualities
            
            constraints += smartOr(possibleEqualities)
            
            k += 1
        }
        
        constraints.toSet
    }
}
