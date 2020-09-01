package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

// An immutable view to look at the current usage of domain elements.
// Sequences of domain elements are all returned in numerical order.
class StalenessState private (
    val sorts: Set[Sort],
    scopeMap: Map[Sort, Int],
    staleMap: Map[Sort, IndexedSeq[DomainElement]]
) {
    
    def scope(sort: Sort): Int = scopeMap(sort)
    
    def staleValues(sort: Sort): IndexedSeq[DomainElement] = staleMap(sort)
    
    def freshValues(sort: Sort): IndexedSeq[DomainElement] = {
        val stale = staleValues(sort)
        domainElements(sort) filter (!stale.contains(_))
    }
    
    def numFreshValues(sort: Sort): Int = freshValues(sort).size
    
    def existsFreshValue(sort: Sort): Boolean = numFreshValues(sort) > 0
    
    def domainElements(sort: Sort): IndexedSeq[DomainElement] = DomainElement.range(1 to scope(sort), sort)
    
    def createTrackerWithState: StalenessTracker = StalenessTracker.create(sorts, staleMap, scopeMap)
}

object StalenessState {
    def apply(
        sorts: Set[Sort],
        scopes: Map[Sort, Int],
        staleElems: Map[Sort, Seq[DomainElement]]
    ): StalenessState = {
        
        val staleMap = staleElems.map{
            case(sort, seq) => sort -> seq.toIndexedSeq.sorted
        }.toMap
        new StalenessState(sorts, scopes, staleMap)
    }
    
    def apply(
        sorts: Set[Sort],
        scopes: Map[Sort, Int],
        staleElems: Map[Sort, Set[DomainElement]]
    )(implicit d: DummyImplicit): StalenessState = {

        val staleMap = staleElems.map{
            case(sort, seq) => sort -> seq.toIndexedSeq.sorted
        }.toMap
        new StalenessState(sorts, scopes, staleMap)
    }
}
