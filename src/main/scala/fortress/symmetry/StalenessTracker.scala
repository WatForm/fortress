package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

import scala.collection.mutable

class StalenessTracker private (
    val sorts: Set[Sort],
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
    
    def state: StalenessState = StalenessState(sorts, scopes, staleElements)
}

object StalenessTracker {
    def create(theory: Theory, scopes: Map[Sort, Int]): StalenessTracker = {
        // Determine which domain elements have been used in the original theory
        val allStaleDomainElements: Set[DomainElement] = theory.axioms flatMap (_.domainElements)
        val staleMap: Map[Sort, Set[DomainElement]] = {
            for (sort <- theory.sorts if !sort.isBuiltin) yield {
                val set = allStaleDomainElements filter (_.sort == sort)
                sort -> set
            }
        }.toMap
        new StalenessTracker(theory.sorts, staleMap, scopes)
    }
    
    def create(sorts: Set[Sort], staleDomainElems: Map[Sort, Seq[DomainElement]], scopes: Map[Sort, Int]): StalenessTracker = {
        val map = staleDomainElems map {
            case (sort, domElems) => sort -> domElems.toSet
        }
        new StalenessTracker(sorts, map, scopes)
    }
}
