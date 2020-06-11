package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._

import scala.collection.mutable

class DomainElementTracker(theory: Theory, scopes: Map[Sort, Int]) {
    // Contains all used domain elements in the theory
    // This data structure is updated over time
    // Note this an immutable map of mutable sets
    val usedDomainElements: Map[Sort, mutable.Set[DomainElement]] = {
        // Determine which domain elements have been used in the original theory
        val allUsedDomainElements: Set[DomainElement] = theory.axioms flatMap (_.domainElements)
        val mapTuples = for (sort <- theory.sorts if !sort.isBuiltin) yield {
            val set = allUsedDomainElements filter (_.sort == sort)
            val mutableSet = mutable.Set(set.toSeq: _*) // Annoying conversion
            (sort, mutableSet)
        }
        mapTuples.toMap
    }
    
    // Marks domain elements as used
    def markUsed(domainElements: Iterable[DomainElement]): Unit = {
        for(de <- domainElements) {
            usedDomainElements(de.sort) += de
        }
    }
    
    // Determines whether this sort has any unused domain elements
    def stillUnusedDomainElements(sort: Sort): Boolean = usedDomainElements(sort).size < scopes(sort)
    // Determines how many unused domain elements this sort has
    def numUnusedDomainElements(sort: Sort): Int = scopes(sort) - usedDomainElements(sort).size
}
