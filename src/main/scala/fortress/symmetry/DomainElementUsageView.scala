package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

// An immutable view to look at the current usage of domain elements.
// Sequences of domain elements are all returned in numerical order.
sealed trait DomainElementUsageView {
    protected def scopeMap: Map[Sort, Int]
    
    protected def usedDomainElementsMap: Map[Sort, IndexedSeq[DomainElement]]
    
    def scope(sort: Sort): Int = scopeMap(sort)
    
    def usedDomainElements(sort: Sort): IndexedSeq[DomainElement] = usedDomainElementsMap(sort)
    
    def unusedDomainElements(sort: Sort): IndexedSeq[DomainElement] = {
        val used = usedDomainElements(sort)
        domainElements(sort) filter (!used.contains(_))
    }
    
    def numUnusedDomainElements(sort: Sort): Int = unusedDomainElements(sort).size
    
    def existsUnusedDomainElements(sort: Sort): Boolean = numUnusedDomainElements(sort) > 0
    
    def domainElements(sort: Sort): IndexedSeq[DomainElement] = DomainElement.range(1 to scope(sort), sort)
    
    def createTracker: DomainElementTracker = DomainElementTracker.create(usedDomainElementsMap, scopeMap)
}

object DomainElementUsageView {
    def apply(
        scopes: Map[Sort, Int],
        usedDomainElems: Map[Sort, Seq[DomainElement]]
    ): DomainElementUsageView = {
        
        object View extends DomainElementUsageView {
            val scopeMap = scopes
            val usedDomainElementsMap = usedDomainElems.map{
                case(sort, seq) => sort -> seq.toIndexedSeq.sortWith(_.index < _.index)
            }.toMap
        }
        View
    }
    
    def apply(
        scopes: Map[Sort, Int],
        usedDomainElems: Map[Sort, Set[DomainElement]]
    )(implicit d: DummyImplicit): DomainElementUsageView = {
        
        object View extends DomainElementUsageView {
            val scopeMap = scopes
            val usedDomainElementsMap = usedDomainElems.map{
                case(sort, seq) => sort -> seq.toIndexedSeq.sortWith(_.index < _.index)
            }.toMap
        }
        View
    }
}
