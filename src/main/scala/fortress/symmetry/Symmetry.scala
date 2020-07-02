package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors

import scala.collection.mutable

object Symmetry {
    private[this] type ArgList = Seq[DomainElement]
    
    def csConstantRangeRestrictions(sort: Sort, constants: IndexedSeq[AnnotatedVar], scope: Int,
        usedValues: IndexedSeq[DomainElement]): Set[RangeRestriction] = {
        Errors.precondition(!sort.isBuiltin)
        Errors.precondition(constants.forall(_.sort == sort))
        Errors.precondition(usedValues.forall(_.sort == sort))
        Errors.precondition(usedValues.forall(_.index <= scope))
        Errors.precondition(usedValues.size < scope)
        
        val unusedValues = (for(i <- 1 to scope) yield DomainElement(i, sort)) diff usedValues
        
        val n = constants.size
        val m = unusedValues.size
        val r = scala.math.min(n, m)
        
        val constraints: Seq[RangeRestriction] =
            for (k <- 0 to (r - 1)) // Enumerate constants
            yield {
                val c_k = constants(k).variable
            
                val possibleValues: Seq[DomainElement] =
                    usedValues ++ // Could be any of the used values
                    unusedValues.take(k + 1) // One of the first k + 1 unused values (recall, k starts at 0)
            
                RangeRestriction(c_k, possibleValues)
            }
        
        constraints.toSet
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
        
        val implications = for {
            i <- 0 to (r - 1) // Enumerates constants
            j <- 1 to i // Enumerates values, starting with the second
        } yield {
            val c_i = constants(i).variable
            
            val precedingConstants = constants.take(i) map (_.variable) // Recall indexing starts at 0
            
            (c_i === unusedValues(j)) ==> (unusedValues(j - 1) equalsOneOfFlip precedingConstants)
        }
        
        implications.toSet
    }
    
    // Produces matching output to csConstantEqualities - meant to be used at same
    // time with same input
    def csConstantImplicationsSimplified(sort: Sort, constants: IndexedSeq[AnnotatedVar], scope: Int,
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
        
        val implications = for {
            i <- 0 to (r - 1) // Enumerates constants
            j <- 1 to i // Enumerates values, starting with the second
        } yield {
            val c_i = constants(i).variable
            
            val possiblePrecedingConstants = for(l <- (j - 1) to (i - 1)) yield constants(l).variable
            
            (c_i === unusedValues(j)) ==> (unusedValues(j - 1) equalsOneOfFlip possiblePrecedingConstants)
        }
        
        implications.toSet
    }
    
    def drdFunctionRangeRestrictions(f: FuncDecl, scopes: Map[Sort, Int],
        usedResultValues: IndexedSeq[DomainElement]): Set[RangeRestriction] = {
        Errors.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.precondition(!f.resultSort.isBuiltin)
        Errors.precondition(usedResultValues.forall(_.sort == f.resultSort))
        Errors.precondition(usedResultValues.forall(_.index <= scopes(f.resultSort)))
        Errors.precondition(usedResultValues.size < scopes(f.resultSort))
        Errors.precondition(!(f.argSorts contains f.resultSort))
        
        val unusedResultValues: IndexedSeq[DomainElement] = {
            val allResultValues = for(i <- 1 to scopes(f.resultSort)) yield DomainElement(i, f.resultSort)
            allResultValues diff usedResultValues
        }
        
        val m = unusedResultValues.size
        
        val argumentListsIterable: Iterable[ArgList] =
            new fortress.util.ArgumentListGenerator(scopes)
            .allArgumentListsOfFunction(f)
            .take(m) // Take up to m of them,  for efficiency since we won't need more than this - the argument list generator does not generate arguments
            // until they are needed
        
        val argumentLists = argumentListsIterable.toIndexedSeq
        
        val n = argumentLists.size
        
        val r = scala.math.min(m, n)
        
        val constraints: Seq[RangeRestriction] =
            for (k <- 0 to (r - 1)) // Enumerate argument vectors
            yield {
                val argList = argumentLists(k)
                val possibleResultValues: Seq[DomainElement] = 
                    usedResultValues ++ // Could be any of the used values
                    unusedResultValues.take(k + 1) // One of the first k + 1 unused values (recall, k starts at 0)
                RangeRestriction(App(f.name, argList), possibleResultValues)
            }
        
        constraints.toSet
    }
    
    // Produces matching output to drdFunctionEqualities - meant to be used at same
    // time with same input
    def drdFunctionImplications(f: FuncDecl, scopes: Map[Sort, Int],
        usedResultValues: IndexedSeq[DomainElement]): Set[Term] = {
        Errors.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.precondition(!f.resultSort.isBuiltin)
        Errors.precondition(usedResultValues.forall(_.sort == f.resultSort))
        Errors.precondition(usedResultValues.forall(_.index <= scopes(f.resultSort)))
        Errors.precondition(usedResultValues.size < scopes(f.resultSort))
        Errors.precondition(!(f.argSorts contains f.resultSort))
        
        val unusedResultValues: IndexedSeq[DomainElement] = {
            val allResultValues = for(i <- 1 to scopes(f.resultSort)) yield DomainElement(i, f.resultSort)
            allResultValues diff usedResultValues
        }
        
        val m = unusedResultValues.size
        
        val argumentListsIterable: Iterable[ArgList] =
            new fortress.util.ArgumentListGenerator(scopes)
            .allArgumentListsOfFunction(f)
            .take(m) // Take up to m of them,  for efficiency since we won't need more than this - the argument list generator does not generate arguments
            // until they are needed
        
        val argumentLists = argumentListsIterable.toIndexedSeq
        val applications: IndexedSeq[Term] = argumentLists map (App(f.name, _))
        
        val n = applications.size
        
        val r = scala.math.min(m, n)
        
        val implications = for {
            i <- 0 to (r - 1) // Enumerates argVectors
            j <- 1 to i // Enumerates result values, starting with the second
        } yield {
            val app_i = applications(i)
            
            val precedingApps = applications.take(i) // Recall indexing starts at 0
            
            (app_i === unusedResultValues(j)) ==> (unusedResultValues(j - 1) equalsOneOfFlip precedingApps)
        }
        
        implications.toSet
    }
    
    // Produces matching output to drdFunctionEqualities - meant to be used at same
    // time with same input
    def drdFunctionImplicationsSimplified(f: FuncDecl, scopes: Map[Sort, Int],
        usedResultValues: IndexedSeq[DomainElement]): Set[Term] = {
        Errors.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.precondition(!f.resultSort.isBuiltin)
        Errors.precondition(usedResultValues.forall(_.sort == f.resultSort))
        Errors.precondition(usedResultValues.forall(_.index <= scopes(f.resultSort)))
        Errors.precondition(usedResultValues.size < scopes(f.resultSort))
        Errors.precondition(!(f.argSorts contains f.resultSort))
        
        val unusedResultValues: IndexedSeq[DomainElement] = {
            val allResultValues = for(i <- 1 to scopes(f.resultSort)) yield DomainElement(i, f.resultSort)
            allResultValues diff usedResultValues
        }
        
        val m = unusedResultValues.size
        
        val argumentListsIterable: Iterable[ArgList] =
            new fortress.util.ArgumentListGenerator(scopes)
            .allArgumentListsOfFunction(f)
            .take(m) // Take up to m of them,  for efficiency since we won't need more than this - the argument list generator does not generate arguments
            // until they are needed
        
        val argumentLists = argumentListsIterable.toIndexedSeq
        val applications: IndexedSeq[Term] = argumentLists map (App(f.name, _))
        
        val n = applications.size
        
        val r = scala.math.min(m, n)
        
        val implications = for {
            i <- 0 to (r - 1) // Enumerates argVectors
            j <- 1 to i // Enumerates result values, starting with the second
        } yield {
            val app_i = applications(i)
            
            val possiblePrecedingApps = for(l <- (j - 1) to (i - 1)) yield applications(l)
            
            (app_i === unusedResultValues(j)) ==> (unusedResultValues(j - 1) equalsOneOfFlip possiblePrecedingApps)
        }
        
        implications.toSet
    }
    
    private[this] def predicateImplicationChain(P: FuncDecl, argLists: IndexedSeq[ArgList]): Seq[Term] = {
        for(i <- 1 to (argLists.size - 1)) yield {
            App(P.name, argLists(i)) ==> App(P.name, argLists(i - 1))
        }
    }
    
    // I think better symmetry breaking can be done on predicates.
    // This is about as good as we can do for predicates of the form P: A -> Bool
    // Or P: A x A -> Bool, but I think more can be done for e.g. P: A x B x A -> Bool
    // The issue is the smallest element comment below.
    def predicateImplications_OLD(P: FuncDecl, scopes: Map[Sort, Int],
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
        
        Errors.precondition(P.argSorts forall (unusedValues(_).size >= 2))
        
        val r = (unusedValues.values map (_.size)).min // Smallest number of unused values
        
        // Generate lists of arguments in the order we will use them for symmetry breaking
        // e.g. If P: A x B x A -> Bool, gives Seq[(a1, b1, a1), (a2, b2, a2), ...]
        
        val argLists: IndexedSeq[ArgList] = for(i <- 0 to (r - 1)) yield {
            P.argSorts map (sort => unusedValues(sort)(i))
        }
        
        predicateImplicationChain(P, argLists).toSet
    }
    
    def predicateImplications(P: FuncDecl, scopes: Map[Sort, Int],
        usedValues: Map[Sort, IndexedSeq[DomainElement]]): Set[Term] = {
            Errors.precondition(P.resultSort == BoolSort)
            Errors.precondition(P.argSorts forall (!_.isBuiltin))
            Errors.precondition(P.argSorts forall (sort => usedValues(sort).size <= scopes(sort)))
            
            val tracker = DomainElementTracker.create(usedValues, scopes)
            
            Errors.precondition(P.argSorts exists (tracker.numUnusedDomainElements(_) >= 2))
            
            def fillArgList(sort: Sort, d: DomainElement): ArgList = {
                Errors.precondition(d.sort == sort)
                for(s <- P.argSorts) yield {
                    if(s == sort) d
                    else DomainElement(1, s) // TODO can we make a smarter selection for the other elements?
                }
            }
            
            val constraints = new mutable.ListBuffer[Term]
            
            while(P.argSorts exists (tracker.numUnusedDomainElements(_) >= 2)) {
                val sort = (P.argSorts find (tracker.numUnusedDomainElements(_) >= 2)).get
                val r = tracker.numUnusedDomainElements(sort)
                val argLists: IndexedSeq[ArgList] = for(i <- 0 to (r - 1)) yield {
                    fillArgList(sort, tracker.unusedDomainElements(sort)(i))
                }
                val implications = predicateImplicationChain(P, argLists)
                constraints ++= implications
                tracker.markUsed(implications flatMap (_.domainElements))
            }
            
            constraints.toSet
        }
    
    // Only need scope for result value
    // I think more symmetry breaking can be done here
    def csFunctionExtRangeRestrictions(f: FuncDecl, resultScope: Int,
        usedResultValues: IndexedSeq[DomainElement]): Set[RangeRestriction] = {
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
            val constraints: Seq[RangeRestriction] = for(i <- 0 to (m - 2)) yield {
                val resVal = unusedResultValues(i)
                val argList = constructArgList(resVal)
                
                val possibleResultValues =
                    usedResultValues ++
                    unusedResultValues.take(i + 2)
                
                RangeRestriction(App(f.name, argList), possibleResultValues)
            }
            
            constraints.toSet
        }
    
}
