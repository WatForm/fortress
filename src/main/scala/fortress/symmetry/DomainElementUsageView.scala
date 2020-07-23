package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

// An immutable view to look at the current usage of domain elements.
// Sequences of domain elements are all returned in numerical order.
trait DomainElementUsageView {
    def scope(sort: Sort): Int
    
    def usedDomainElements(sort: Sort): IndexedSeq[DomainElement]
    
    def unusedDomainElements(sort: Sort): IndexedSeq[DomainElement] = {
        val used = usedDomainElements(sort)
        domainElements(sort) filter (!used.contains(_))
    }
    
    def numUnusedDomainElements(sort: Sort): Int = unusedDomainElements(sort).size
    
    def existsUnusedDomainElements(sort: Sort): Boolean = numUnusedDomainElements(sort) > 0
    
    def domainElements(sort: Sort): IndexedSeq[DomainElement] = {
        (1 to scope(sort)) map { i => DomainElement(i, sort) }
    }
}

object DomainElementUsageView {
    def apply(
        scopes: Map[Sort, Int],
        usedDomainElems: Map[Sort, Seq[DomainElement]]
    ): DomainElementUsageView = {
        
        object View extends DomainElementUsageView {
            def scope(sort: Sort): Int = scopes(sort)
            
            def usedDomainElements(sort: Sort): IndexedSeq[DomainElement] = {
                val collection = usedDomainElems(sort)
                domainElements(sort) filter (collection contains _)
            }
        }
        View
    }
    
    def apply(
        scopes: Map[Sort, Int],
        usedDomainElems: Map[Sort, Set[DomainElement]]
    )(implicit d: DummyImplicit): DomainElementUsageView = {
        
        object View extends DomainElementUsageView {
            def scope(sort: Sort): Int = scopes(sort)
            
            def usedDomainElements(sort: Sort): IndexedSeq[DomainElement] = {
                val collection = usedDomainElems(sort)
                domainElements(sort) filter (collection contains _)
            }
        }
        View
    }
}
