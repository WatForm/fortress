package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

import scala.collection.mutable

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
        usedDomainElems: Map[Sort, Seq[DomainElement]] // SHOULD BE IMMUTABLE!!!!!
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
}

class DomainElementTracker private(usedDomainElementsMut: Map[Sort, mutable.Set[DomainElement]], scopes: Map[Sort, Int]) {
    
    // Marks domain elements as used
    def markUsed(domainElements: Iterable[DomainElement]): Unit = {
        for(de <- domainElements) {
            usedDomainElementsMut(de.sort) += de
        }
    }
    
    // Determines whether this sort has any unused domain elements
    def stillUnusedDomainElements(sort: Sort): Boolean = usedDomainElements(sort).size < scopes(sort)
    // Determines how many unused domain elements this sort has
    def numUnusedDomainElements(sort: Sort): Int = scopes(sort) - usedDomainElements(sort).size
    
    def usedDomainElements: Map[Sort, Set[DomainElement]] = usedDomainElementsMut.map{case (sort, mutSet) => sort -> mutSet.toSet}
    
    def unusedDomainElements: Map[Sort, IndexedSeq[DomainElement]] = usedDomainElements.map {
        case (sort, usedVals) => {
            val unusedVals = (for(i <- 1 to scopes(sort)) yield DomainElement(i, sort)) diff usedVals.toSeq
            (sort, unusedVals)
        }
    }
    
    def view: DomainElementUsageView = {
        object View extends DomainElementUsageView {
            def scope(sort: Sort): Int = scopes(sort)
            
            def usedDomainElements(sort: Sort): IndexedSeq[DomainElement] = {
                val set = usedDomainElementsMut(sort)
                domainElements(sort) filter (set contains _)
            }
        }
        View
    }
}

object DomainElementTracker {
    def create(theory: Theory, scopes: Map[Sort, Int]): DomainElementTracker = {
        // Determine which domain elements have been used in the original theory
        val allUsedDomainElements: Set[DomainElement] = theory.axioms flatMap (_.domainElements)
        val mapTuples = for (sort <- theory.sorts if !sort.isBuiltin) yield {
            val set = allUsedDomainElements filter (_.sort == sort)
            val mutableSet = mutable.Set(set.toSeq: _*) // Annoying conversion
            (sort, mutableSet)
        }
        new DomainElementTracker(mapTuples.toMap, scopes)
    }
    
    def create(usedDomainElems: Map[Sort, Seq[DomainElement]], scopes: Map[Sort, Int]) = {
        val map = usedDomainElems map {case (sort, domElems) => sort -> mutable.Set[DomainElement](domElems : _*)}
        new DomainElementTracker(map, scopes)
    }
}
