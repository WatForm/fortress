package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._
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
        
        val equalityConstraints: Seq[Term] =
            for (k <- 0 to (r - 1)) // Enumerate constants
            yield {
                val c_k = constants(k).variable
            
                val possibleValues: Seq[Term] =
                    usedValues ++ // Could be any of the used values
                    unusedValues.take(k + 1) // One of the first k + 1 unused values (recall, k starts at 0)
            
                c_k equalsOneOf possibleValues
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
            k <- 1 to (r - 1); // Enumerates constants, except first
            d <- 1 to k // Enumerates values
        ) yield {
            val c_k = constants(k).variable
            
            val precedingConstants = constants.take(k) map (_.variable) // Recall indexing starts at 0
            
            (c_k === unusedValues(d)) ==> (unusedValues(d - 1) equalsOneOfFlip precedingConstants)
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
        
        val m = unusedResultValues.size
        
        val argumentListsIterable: Iterable[Seq[DomainElement]] =
            new fortress.util.ArgumentListGenerator(scopes)
            .allArgumentListsOfFunction(f)
            .take(m) // Take up to m of them,  for efficiency since we won't need more than this - the argument list generator does not generate arguments
            // until they are needed
        
        val argumentLists = argumentListsIterable.toIndexedSeq
        
        val n = argumentLists.size
        
        val r = scala.math.min(m, n)
        
        val equalityConstraints: Seq[Term] =
            for (k <- 0 to (r - 1)) // Enumerate argument vectors
            yield {
                val argList = argumentLists(k)
                val possibleResultValues: Seq[Term] = 
                    usedResultValues ++ // Could be any of the used values
                    unusedResultValues.take(k + 1) // One of the first k + 1 unused values (recall, k starts at 0)
                App(f.name, argList) equalsOneOf possibleResultValues
            }
        
        equalityConstraints.toSet
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
    // I think more symmetry breaking can be done here
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
                    else DomainElement(1, sort) // for other sorts, doesn't matter what values we choose
                })
            }
            
            val m = unusedResultValues.size
            val equalityConstraints: Seq[Term] = for(i <- 0 to (m - 2)) yield {
                val resVal = unusedResultValues(i)
                val argList = constructArgList(resVal)
                
                val possibleResultValues =
                    usedResultValues ++
                    unusedResultValues.take(i + 2)
                
                App(f.name, argList) equalsOneOf possibleResultValues
            }
            
            equalityConstraints.toSet
        }
    
}
