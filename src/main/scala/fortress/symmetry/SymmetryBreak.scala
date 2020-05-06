package fortress.symmetry

import fortress.msfol._
import fortress.util.Errors

object Symmetry {
    
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
            
            Or.smart(possibleEqualities)
        }
        
        equalityConstraints.toSet
    }
    
    // Produces matching output to csConstantEqualities - meant to be used at same
    // time with same input
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
                Or.smart(possibleEqualities)
            )
        }
        
        implications.toSet
    }
    
    def drdFunctionEqualities(f: FuncDecl, scopes: Map[Sort, Int],
        usedResultValues: IndexedSeq[DomainElement]): Set[Term] = {
        Errors.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.precondition(!f.resultSort.isBuiltin)
        Errors.precondition(usedResultValues.forall(_.sort == f.resultSort))
        Errors.precondition(usedResultValues.forall(_.index <= scopes(f.resultSort)))
        Errors.precondition(usedResultValues.size < scopes(f.resultSort))
        Errors.precondition(!(f.argSorts contains f.resultSort))
        
        val unusedResultValues: IndexedSeq[DomainElement] = (for(i <- 1 to scopes(f.resultSort)) yield DomainElement(i, f.resultSort)) diff usedResultValues
        
        val argumentLists = new fortress.util.ArgumentListGenerator(scopes).allArgumentListsOfFunction(f)
        
        // Use TAKE
        
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
            
            constraints += Or.smart(possibleEqualities)
            
            k += 1
        }
        
        constraints.toSet
    }
    
    // Produces matching output to drdFunctionEqualities - meant to be used at same
    // time with same input
    def drdFunctionImplications(f: FuncDecl, scopes: Map[Sort, Int],
        usedResultValues: IndexedSeq[DomainElement]): Set[Term] = ???
    
    // I think better symmetry breaking can be done on predicates.
    // This is about as good as we can do for predicates of the form P: A -> Bool
    // Or P: A x A -> Bool, but I think more can be done for e.g. P: A x B x A -> Bool
    // The issue is the smallest element comment below.
    def predicateImplications(P: FuncDecl, scopes: Map[Sort, Int],
        usedValues: Map[Sort, IndexedSeq[DomainElement]]): Set[Term] = {
        Errors.precondition(P.resultSort == BoolSort)
        Errors.precondition(P.argSorts.forall(!_.isBuiltin))
        Errors.precondition(P.argSorts.forall(sort => usedValues(sort).size <= scopes(sort)))
        
        val unusedValues: Map[Sort, IndexedSeq[DomainElement]] = usedValues.map {
            case (sort, usedVals) => {
                val unusedVals = (for(i <- 1 to scopes(sort)) yield DomainElement(i, sort)) diff usedVals
                (sort, unusedVals)
            }
        }
        
        val r = (unusedValues.values map (_.size)).min // Smallest number of unused values
        
        // Generate lists of arguments in the order we will use them for symmetry breaking
        // e.g. If P: A x B x A -> Bool, gives Seq[(a1, b1, a1), (a2, b2, a2), ...]
        type ArgList = Seq[DomainElement]
        val argLists: IndexedSeq[ArgList] = for(i <- 0 to (r - 1)) yield {
            P.argSorts map (sort => unusedValues(sort)(i))
        }
        
        val implications = for(i <- 1 to (argLists.size - 1)) yield {
            App(P.name, argLists(i)) ==> App(P.name, argLists(i - 1))
        }
        
        implications.toSet
    }
    
    // Only need scope for result value
    def csFunctionExtEqualities(f: FuncDecl, resultScope: Int,
        usedResultValues: IndexedSeq[DomainElement]): Set[Term] = {
            Errors.precondition(f.argSorts.forall(!_.isBuiltin))
            Errors.precondition(!f.resultSort.isBuiltin)
            Errors.precondition(usedResultValues.forall(_.sort == f.resultSort))
            Errors.precondition(usedResultValues.forall(_.index <= resultScope))
            Errors.precondition(usedResultValues.size < resultScope)
            Errors.precondition(f.argSorts contains f.resultSort)
            
            val unusedResultValues: IndexedSeq[DomainElement] = (for(i <- 1 to resultScope) yield DomainElement(i, f.resultSort)) diff usedResultValues
            
            // We fix particular values for the sorts not in the output
            // These stay the same for all argument lists we symmetry break using
            // (you don't have to fix particular values, but you can)
            
            // Construct an argument list given the result value we are using
            // e.g. if f: A x B x A x D -> A,
            // given a2 it will yield: (a2, b1, a2, d1)
            // given a3 it will yield: (a3, b1, a3, d1)
            def constructArgList(resVal: DomainElement): Seq[DomainElement] = {
                Errors.precondition(resVal.sort == f.resultSort)
                f.argSorts map (sort => {
                    if(sort == f.resultSort) resVal
                    else DomainElement(1, sort)
                })
            }
            
            val m = unusedResultValues.size
            val constraints = for(i <- 0 to (m - 2)) yield {
                val resVal = unusedResultValues(i)
                val argList = constructArgList(resVal)
                val app = App(f.name, argList)
                val possibleUsedEqualities = for(v <- usedResultValues) yield {
                    app === v
                }
                val possibleUnusedEqualities = for(j <- 0 to (i + 1)) yield { // i + 1 necessary
                    app === unusedResultValues(j)
                }
                val possibleEqualities = possibleUsedEqualities ++ possibleUnusedEqualities
                Or.smart(possibleEqualities)
            }
            
            constraints.toSet
        }
    
}
