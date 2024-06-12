package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations._
import fortress.problemstate._
import fortress.sortinference._
import fortress.util.Errors

// An immutable view to look at the current usage of domain elements.
// Sequences of domain elements are all returned in numerical order.
class StalenessState private (
    val sorts: Set[Sort],
    scopeMap: Map[Sort, Scope],
    staleMap: Map[Sort, IndexedSeq[DomainElement]],
    // Were the domain elements filtered via the pattern optimization?
    patternOptimization: Boolean = false,
) {
    
    def scope(sort: Sort): Scope = scopeMap(sort)
    
    def staleValues(sort: Sort): IndexedSeq[DomainElement] = staleMap(sort)

    // testing only
    def allStaleValues: Map[Sort, IndexedSeq[DomainElement]] = staleMap
    
    def freshValues(sort: Sort): IndexedSeq[DomainElement] = {
        val stale = staleValues(sort)
        domainElements(sort) filter (!stale.contains(_))
    }
    
    def numFreshValues(sort: Sort): Int = freshValues(sort).size
    
    def existsFreshValue(sort: Sort): Boolean = numFreshValues(sort) > 0
    
    def domainElements(sort: Sort): IndexedSeq[DomainElement] = {
        val sc = scope(sort)
        DomainElement.range(1 to sc.size , sort)
    }
    
    def createTrackerWithState: StalenessTracker = if (patternOptimization)
        StalenessTracker.createWithPatternOptimization(sorts, staleMap, scopeMap)
    else StalenessTracker.create(sorts, staleMap, scopeMap)

    def afterSubstitution(sortSubstitution: SortSubstitution): StalenessState = {
        val newSorts = sorts map sortSubstitution
        val inverse: Sort => Set[Sort] = sortSubstitution.inverse
        val newScopeMap: Map[Sort, Scope] = {
            for(sort <- newSorts) yield {
                val preImage = inverse(sort).filter( item => scopeMap.contains(item) )

                val M: Int = preImage.map( scope(_).size ).max

                var s = scope(preImage.head)
                for (item <- preImage) {
                    if( scope(item).size == M ) {
                        s = scope(item)
                    }
                }
                sort -> s
            }
        }.toMap
        val newStaleMap: Map[Sort, IndexedSeq[DomainElement]] = {
            for(sort <- newSorts) yield {
                sort -> {
                    val preImage = inverse(sort)
                    val domElems: Set[DomainElement] = for {
                        s <- preImage
                        de <- staleValues(s)
                        de_sub = sortSubstitution.applyDE(de)
                    } yield de_sub
                    domElems.toIndexedSeq.sorted
                }
            }
        }.toMap
        StalenessState(newSorts, newScopeMap, newStaleMap, patternOptimization)
    }
}

object StalenessState {
    def apply(
        sorts: Set[Sort],
        scopes: Map[Sort, Scope],
        staleElems: Map[Sort, Seq[DomainElement]],
        patternOptimization: Boolean = false,
    ): StalenessState = {
        
        val staleMap = staleElems.map{
            case(sort, seq) => sort -> seq.toIndexedSeq.sorted
        }.toMap
        new StalenessState(sorts, scopes, staleMap, patternOptimization)
    }
    
    def apply(
        sorts: Set[Sort],
        scopes: Map[Sort, Scope],
        staleElems: Map[Sort, Set[DomainElement]]
    )(implicit d: DummyImplicit): StalenessState = {

        val staleMap = staleElems.map{
            case(sort, seq) => sort -> seq.toIndexedSeq.sorted
        }.toMap
        new StalenessState(sorts, scopes, staleMap)
    }

    def apply(
        sorts: Set[Sort],
        scopes: Map[Sort, Scope],
        staleElems: Map[Sort, Set[DomainElement]],
        patternOptimization: Boolean,
    )(implicit d: DummyImplicit): StalenessState = {

        val staleMap = staleElems.map{
            case(sort, seq) => sort -> seq.toIndexedSeq.sorted
        }.toMap
        new StalenessState(sorts, scopes, staleMap, patternOptimization)
    }
}
