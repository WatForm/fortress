package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

import scala.collection.mutable

class DomainElementTracker private (
    private var staleElements: Map[Sort, Set[DomainElement]],
    scopes: Map[Sort, Int]
) {
    
    // Marks domain elements as used
    def markStale(domainElements: Iterable[DomainElement]): Unit = {
        for(de <- domainElements) {
            val sort = de.sort
            staleElements += (sort -> (staleElements(sort) + de))
        }
    }
    
    def view: DomainElementUsageView = DomainElementUsageView(scopes, staleElements)
}

object DomainElementTracker {
    def create(theory: Theory, scopes: Map[Sort, Int]): DomainElementTracker = {
        // Determine which domain elements have been used in the original theory
        val allStaleDomainElements: Set[DomainElement] = theory.axioms flatMap (_.domainElements)
        val mapTuples = for (sort <- theory.sorts if !sort.isBuiltin) yield {
            val set = allStaleDomainElements filter (_.sort == sort)
            sort -> set
        }
        new DomainElementTracker(mapTuples.toMap, scopes)
    }
    
    def create(staleDomainElems: Map[Sort, Seq[DomainElement]], scopes: Map[Sort, Int]) = {
        val map = staleDomainElems map {
            case (sort, domElems) => sort -> domElems.toSet
        }
        new DomainElementTracker(map, scopes)
    }
}
