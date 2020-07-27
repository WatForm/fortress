package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.util.Errors
import fortress.util.Extensions._

import scala.collection.mutable

object Symmetry {
    private[this] type ArgList = Seq[Value]
    
    def csConstantRangeRestrictions(
        sort: Sort,
        constants: IndexedSeq[AnnotatedVar],
        deView: DomainElementUsageView
    ): Set[RangeRestriction] = {
        
        Errors.precondition(!sort.isBuiltin)
        Errors.precondition(constants.forall(_.sort == sort))
        
        val n = constants.size
        val m = deView.numUnusedDomainElements(sort)
        val r = scala.math.min(n, m)
        
        val constraints: Seq[RangeRestriction] =
            for (k <- 0 to (r - 1)) // Enumerate constants
            yield {
                val c_k = constants(k).variable
            
                val possibleValues: Seq[DomainElement] =
                    deView.usedDomainElements(sort) ++ // Could be any of the used values
                    deView.unusedDomainElements(sort).take(k + 1) // One of the first k + 1 unused values (recall, k starts at 0)
            
                RangeRestriction(c_k, possibleValues)
            }
        
        constraints.toSet
    }
    
    // Produces matching output to csConstantEqualities - meant to be used at same
    // time with same input
    def csConstantImplications(
        sort: Sort,
        constants: IndexedSeq[AnnotatedVar],
        deView: DomainElementUsageView,
    ): Set[Term] = {
        
        Errors.precondition(!sort.isBuiltin)
        Errors.precondition(constants.forall(_.sort == sort))
        
        val unusedValues = deView.unusedDomainElements(sort)
        
        val n = constants.size
        val m = deView.numUnusedDomainElements(sort)
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
    def csConstantImplicationsSimplified(
        sort: Sort,
        constants: IndexedSeq[AnnotatedVar],
        deView: DomainElementUsageView
    ): Set[Term] = {
        
        Errors.precondition(!sort.isBuiltin)
        Errors.precondition(constants.forall(_.sort == sort))
        
        val unusedValues = deView.unusedDomainElements(sort)
        
        val n = constants.size
        val m = deView.numUnusedDomainElements(sort)
        val r = scala.math.min(n, m)
        
        val implications = for {
            i <- 0 to (r - 1) // Enumerates constants
            j <- 1 to i // Enumerates values, starting with the second
        } yield {
            val c_i = constants(i).variable
            
            val possiblePrecedingConstants = constants.rangeSlice((j - 1) to (i - 1)).map(_.variable)
            
            (c_i === unusedValues(j)) ==> (unusedValues(j - 1) equalsOneOfFlip possiblePrecedingConstants)
        }
        
        implications.toSet
    }
    
    def drdFunctionRangeRestrictions(
        f: FuncDecl,
        deView: DomainElementUsageView
    ): Set[RangeRestriction] = {
        
        Errors.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.precondition(!f.resultSort.isBuiltin)
        Errors.precondition(f.isDomainRangeDistinct)
        
        val unusedResultValues: IndexedSeq[DomainElement] = deView.unusedDomainElements(f.resultSort)
        val usedResultValues = deView.usedDomainElements(f.resultSort)
        
        val m = unusedResultValues.size
        
        val argumentListsIterable: Iterable[ArgList] =
            new fortress.util.ArgumentListGenerator(deView.scope(_))
            .allArgumentListsOfFunction(f)
            .take(m) // Take up to m of them, for efficiency since we won't need more than this - the argument list generator does not generate arguments
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
    def drdFunctionImplications(
        f: FuncDecl,
        deView: DomainElementUsageView
    ): Set[Term] = {
        
        Errors.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.precondition(!f.resultSort.isBuiltin)
        Errors.precondition(!(f.argSorts contains f.resultSort))
        
        val unusedResultValues: IndexedSeq[DomainElement] = deView.unusedDomainElements(f.resultSort)
        
        val m = unusedResultValues.size
        
        val argumentListsIterable: Iterable[ArgList] =
            new fortress.util.ArgumentListGenerator(deView.scope(_))
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
    def drdFunctionImplicationsSimplified(
        f: FuncDecl,
        deView: DomainElementUsageView
    ): Set[Term] = {
        
        Errors.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.precondition(!f.resultSort.isBuiltin)
        Errors.precondition(!(f.argSorts contains f.resultSort))
        Errors.precondition(f.isDomainRangeDistinct)
        
        val unusedResultValues: IndexedSeq[DomainElement] = deView.unusedDomainElements(f.resultSort)
        
        val m = unusedResultValues.size
        
        val argumentListsIterable: Iterable[ArgList] =
            new fortress.util.ArgumentListGenerator(deView.scope(_))
            .allArgumentListsOfFunction(f)
            .take(m) // Take up to m of them, for efficiency since we won't need more than this - the argument list generator does not generate arguments
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
            val possiblePrecedingApps = applications.rangeSlice((j - 1) to (i - 1))
            (app_i === unusedResultValues(j)) ==> (unusedResultValues(j - 1) equalsOneOfFlip possiblePrecedingApps)
        }
        
        implications.toSet
    }
    
    def sortLtDefinition(sort: Sort, scope: Int): (FuncDecl, Seq[Term])  = {
        val LT = "_LT" + sort.name
        val assertions = for {
            i <- 1 to scope
            j <- 1 to scope
        } yield {
            val app = App(LT, DomainElement(i, sort), DomainElement(j, sort))
            if (i <= j) app
            else Not(app)
        }
        (FuncDecl(LT, sort, sort, BoolSort), assertions)
    }
    
    // I don't think that I can say the constants are ordered
    // No input elements to shuffle
    def rainbowFunctionLT(
        f: FuncDecl,
        deView: DomainElementUsageView
    ): (FuncDecl, Seq[Term], Seq[RangeRestriction]) = {
        
        Errors.precondition(f.argSorts.forall(!_.isBuiltin))
        Errors.precondition(!f.resultSort.isBuiltin)
        
        Errors.precondition(f.isRainbowSorted)
        Errors.precondition(f.arity <= 2)
        Errors.precondition(f.argSorts forall (deView.usedDomainElements(_).isEmpty))
        Errors.precondition(deView.usedDomainElements(f.resultSort).isEmpty)
        Errors.precondition(f.argSorts.forall(deView.scope(_) >= 2))
        Errors.precondition(deView.scope(f.resultSort) >= 2)
        
        val (ltDecl, ltDefn) = sortLtDefinition(f.resultSort, deView.scope(f.resultSort))
        
        val LT = ltDecl.name
        
        val (constraints, rangeRestrictions): (Seq[Term], Seq[RangeRestriction]) = f match {
            // Unary
            case FuncDecl(fname, Seq(argSort), resultSort) => {
                // Ordering constraints
                val ltConstraints: Seq[Term] = for(i <- 1 until deView.scope(argSort)) yield {
                    App(LT,
                        App(fname, DomainElement(i, argSort)),
                        App(fname, DomainElement(i + 1, argSort))
                    )
                }
                
                val drdRangeRestrictions: Seq[RangeRestriction] = drdFunctionRangeRestrictions(f, deView).toSeq
                val drdImplicationsSimplified: Seq[Term] = drdFunctionImplicationsSimplified(f, deView).toSeq
                
                (ltConstraints ++ drdImplicationsSimplified, drdRangeRestrictions)
            }
            // Binary
            case FuncDecl(fname, Seq(argSort1, argSort2), resultSort) => {
                
                // First argument constraints
                
                // Ordering constraints on first argument
                val ltConstraintsArg1: Seq[Term] = for(i <- 1 until deView.scope(argSort1)) yield {
                    App(LT,
                        App(fname, DomainElement(i, argSort1), DomainElement(1, argSort2)),
                        App(fname, DomainElement(i + 1, argSort1), DomainElement(1, argSort2))
                    )
                }
                
                // Have to make DRD constraints manually, otherwise:
                // 1. ordering might not match what we want
                // 2. if scope(resultSort) > scope(argSort1), the constraints will spill over into the second
                // value of argSort2, which is not what we want because then we can't justify "shuffling"
                
                val r1 = scala.math.min(deView.scope(argSort1), deView.scope(resultSort))
                
                val drdRangeRestrictions: Seq[RangeRestriction] = for(i <- 1 to r1) yield {
                    RangeRestriction(
                        App(fname, DomainElement(i, argSort1), DomainElement(1, argSort2)),
                        DomainElement.range(1 to i, resultSort)
                    )
                }
                
                val drdImplicationsSimplified: Seq[Term] = for {
                    i <- 1 to r1
                    j <- 2 to i
                } yield {
                    val lhs = App(fname, DomainElement(i, argSort1), DomainElement(1, argSort2)) === DomainElement(j, resultSort)
                    val rhs = DomainElement(j - 1, resultSort) equalsOneOfFlip DomainElement.range((j - 1) to (i - 1), argSort1).map(App(fname, _, DomainElement(1, argSort2)))
                    lhs ==> rhs
                }
                
                // Second argument constraints
                val ltConstraintsArg2: Seq[Term] = for(i <- 2 until deView.scope(argSort2)) yield {
                    App(LT,
                        App(fname, DomainElement(1, argSort1), DomainElement(i, argSort2)),
                        App(fname, DomainElement(1, argSort1), DomainElement(i + 1, argSort2))
                    )
                }
                
                (ltConstraintsArg1 ++ ltConstraintsArg2 ++ drdImplicationsSimplified, drdRangeRestrictions)
            }
            // Other
            case _ => (???, ???)
        }
        
        (ltDecl, ltDefn ++ constraints, rangeRestrictions)
    }
    
    private[this] def predicateImplicationChain(
        P: FuncDecl,
        argLists: IndexedSeq[ArgList]
    ): Seq[Term] = {
        
        for(i <- 1 to (argLists.size - 1)) yield {
            App(P.name, argLists(i)) ==> App(P.name, argLists(i - 1))
        }
    }
    
    // I think better symmetry breaking can be done on predicates.
    // This is about as good as we can do for predicates of the form P: A -> Bool
    // Or P: A x A -> Bool, but I think more can be done for e.g. P: A x B x A -> Bool
    // The issue is the smallest element comment below.
    def predicateImplications_OLD(
        P: FuncDecl,
        deView: DomainElementUsageView
    ): Set[Term] = {
        
        Errors.precondition(P.resultSort == BoolSort)
        Errors.precondition(P.argSorts.forall(!_.isBuiltin))
        
        Errors.precondition(P.argSorts forall (deView.numUnusedDomainElements(_) >= 2))
        
        val r = (P.argSorts map (deView.numUnusedDomainElements(_))).min // Smallest number of unused values
        
        // Generate lists of arguments in the order we will use them for symmetry breaking
        // e.g. If P: A x B x A -> Bool, gives Seq[(a1, b1, a1), (a2, b2, a2), ...]
        
        val argLists: IndexedSeq[ArgList] = for(i <- 0 to (r - 1)) yield {
            P.argSorts map (sort => deView.unusedDomainElements(sort)(i))
        }
        
        predicateImplicationChain(P, argLists).toSet
    }
    
    def predicateImplications(
        P: FuncDecl,
        deView: DomainElementUsageView
    ): Set[Term] = {
            
            Errors.precondition(P.resultSort == BoolSort)
            Errors.precondition(P.argSorts forall (!_.isBuiltin))
            Errors.precondition(P.argSorts exists (deView.numUnusedDomainElements(_) >= 2))
            
            val tracker = deView.createTracker
            
            def fillArgList(sort: Sort, d: DomainElement): ArgList = {
                Errors.precondition(d.sort == sort)
                for(s <- P.argSorts) yield {
                    if(s == sort) d
                    else DomainElement(1, s) // TODO can we make a smarter selection for the other elements?
                }
            }
            
            val constraints = new mutable.ListBuffer[Term]
            
            while(P.argSorts exists (tracker.view.numUnusedDomainElements(_) >= 2)) {
                val sort = (P.argSorts find (tracker.view.numUnusedDomainElements(_) >= 2)).get
                val r = tracker.view.numUnusedDomainElements(sort)
                val argLists: IndexedSeq[ArgList] = for(i <- 0 to (r - 1)) yield {
                    fillArgList(sort, tracker.view.unusedDomainElements(sort)(i))
                }
                val implications = predicateImplicationChain(P, argLists)
                constraints ++= implications
                tracker.markUsed(implications flatMap (_.domainElements))
            }
            
            constraints.toSet
        }
    
    // I think more symmetry breaking can be done here
    def csFunctionExtRangeRestrictions(
        f: FuncDecl,
        deView: DomainElementUsageView
    ): Set[RangeRestriction] = {
            
            Errors.precondition(f.argSorts.forall(!_.isBuiltin))
            Errors.precondition(!f.resultSort.isBuiltin)
            Errors.precondition(f.argSorts contains f.resultSort)
            Errors.precondition(!f.isDomainRangeDistinct)
            
            val unusedResultValues: IndexedSeq[DomainElement] = deView.unusedDomainElements(f.resultSort)
            val usedResultValues: IndexedSeq[DomainElement] = deView.usedDomainElements(f.resultSort)
            
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
