package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

// An immutable view to look at the current usage of domain elements.
// Sequences of domain elements are all returned in numerical order.
class DomainElementUsageView private (
    private val scopeMap: Map[Sort, Int],
    private val staleMap: Map[Sort, IndexedSeq[DomainElement]]
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
    
    def createTracker: DomainElementTracker = DomainElementTracker.create(staleMap, scopeMap)
}

object DomainElementUsageView {
    def apply(
        scopes: Map[Sort, Int],
        staleElems: Map[Sort, Seq[DomainElement]]
    ): DomainElementUsageView = {
        
        val staleMap = staleElems.map{
            case(sort, seq) => sort -> seq.toIndexedSeq.sorted
        }.toMap
        new DomainElementUsageView(scopes, staleMap)
    }
    
    def apply(
        scopes: Map[Sort, Int],
        staleElems: Map[Sort, Set[DomainElement]]
    )(implicit d: DummyImplicit): DomainElementUsageView = {

        val staleMap = staleElems.map{
            case(sort, seq) => sort -> seq.toIndexedSeq.sorted
        }.toMap
        new DomainElementUsageView(scopes, staleMap)
    }
}
