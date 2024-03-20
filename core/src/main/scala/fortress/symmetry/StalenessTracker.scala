package fortress.symmetry

import fortress.msfol._
import fortress.operations.PortusPatternAccumulator
import fortress.operations.TermOps._
import fortress.problemstate._

import scala.collection.mutable

class StalenessTracker protected (
    val sorts: Set[Sort],
    private var staleElements: Map[Sort, Set[DomainElement]],
    scopes: Map[Sort, Scope]
) {

    // Marks domain elements in the term as used
    def markDomainElementsStale(term: Term): Unit = {
        for (de <- term.domainElements) {
            val sort = de.sort
            staleElements += (sort -> (staleElements(sort) + de))
        }
    }

    protected def extractDomainElements(term: Term): Set[DomainElement] = term.domainElements

    def state: StalenessState = StalenessState(sorts, scopes, staleElements)
}

class PortusPatternStalenessTracker(
    sorts: Set[Sort],
    staleElements: Map[Sort, Set[DomainElement]],
    scopes: Map[Sort, Scope]
) extends StalenessTracker(sorts, staleElements, scopes) {
    override def extractDomainElements(term: Term): Set[DomainElement] =
        PortusPatternAccumulator.domainElementsExceptPatternIn(term)
}

object StalenessTracker {
    def create(theory: Theory, scopes: Map[Sort, Scope]): StalenessTracker = {
        // Determine which domain elements have been used in the original theory
        val axiomStaleElements: Set[DomainElement] = theory.axioms flatMap (_.domainElements)
        val constDefnStaleElements: Set[DomainElement] = theory.constantDefinitions.flatMap(defn => defn.body.domainElements)
        val fnDefnStaleElements: Set[DomainElement] = theory.constantDefinitions.flatMap(defn => defn.body.domainElements)
        val allStaleDomainElements: Set[DomainElement] = axiomStaleElements union constDefnStaleElements union fnDefnStaleElements
        val staleMap: Map[Sort, Set[DomainElement]] = {
            for (sort <- theory.sorts if !sort.isBuiltin) yield {
                val set = allStaleDomainElements filter (_.sort == sort)
                sort -> set
            }
        }.toMap
        new StalenessTracker(theory.sorts, staleMap, scopes)
    }

    def createWithPatternOptimization(theory: Theory, scopes: Map[Sort, Scope]): PortusPatternStalenessTracker = {
        // Determine which domain elements have been used in the original theory
        println(s"[fortress] creating pattern optimization staleness tracker; theory = ${theory}")
        val allStaleDomainElements: Set[DomainElement] =
            theory.axioms flatMap PortusPatternAccumulator.domainElementsExceptPatternIn
        val staleMap: Map[Sort, Set[DomainElement]] = {
            for (sort <- theory.sorts if !sort.isBuiltin) yield {
                val set = allStaleDomainElements filter (_.sort == sort)
                sort -> set
            }
        }.toMap
        new PortusPatternStalenessTracker(theory.sorts, staleMap, scopes)
    }

    def create(sorts: Set[Sort], staleDomainElems: Map[Sort, Seq[DomainElement]], scopes: Map[Sort, Scope]): StalenessTracker = {
        val map = staleDomainElems map {
            case (sort, domElems) => sort -> domElems.toSet
        }
        new StalenessTracker(sorts, map, scopes)
    }
}
