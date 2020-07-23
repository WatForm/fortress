package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

import scala.collection.mutable

class DomainElementTracker private (
    var usedDomainElements: Map[Sort, Set[DomainElement]],
    scopes: Map[Sort, Int]
) {
    
    // Marks domain elements as used
    def markUsed(domainElements: Iterable[DomainElement]): Unit = {
        for(de <- domainElements) {
            val sort = de.sort
            usedDomainElements += (sort -> (usedDomainElements(sort) + de))
        }
    }
    
    def view: DomainElementUsageView = DomainElementUsageView(scopes, usedDomainElements)
}

object DomainElementTracker {
    def create(theory: Theory, scopes: Map[Sort, Int]): DomainElementTracker = {
        // Determine which domain elements have been used in the original theory
        val allUsedDomainElements: Set[DomainElement] = theory.axioms flatMap (_.domainElements)
        val mapTuples = for (sort <- theory.sorts if !sort.isBuiltin) yield {
            val set = allUsedDomainElements filter (_.sort == sort)
            sort -> set
        }
        new DomainElementTracker(mapTuples.toMap, scopes)
    }
    
    def create(usedDomainElems: Map[Sort, Seq[DomainElement]], scopes: Map[Sort, Int]) = {
        val map = usedDomainElems map {
            case (sort, domElems) => sort -> domElems.toSet
        }
        new DomainElementTracker(map, scopes)
    }
}
