package fortress.symmetry

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations._
import fortress.sortinference._

// An immutable view to look at the current usage of domain elements.
// Sequences of domain elements are all returned in numerical order.
class StalenessState private (
    val sorts: Set[Sort],
    scopeMap: Map[Sort, (Int, Boolean)],
    staleMap: Map[Sort, IndexedSeq[DomainElement]]
) {
    
    def scope(sort: Sort): (Int, Boolean) = scopeMap(sort)
    
    def staleValues(sort: Sort): IndexedSeq[DomainElement] = staleMap(sort)
    
    def freshValues(sort: Sort): IndexedSeq[DomainElement] = {
        val stale = staleValues(sort)
        domainElements(sort) filter (!stale.contains(_))
    }
    
    def numFreshValues(sort: Sort): Int = freshValues(sort).size
    
    def existsFreshValue(sort: Sort): Boolean = numFreshValues(sort) > 0
    
    def domainElements(sort: Sort): IndexedSeq[DomainElement] = DomainElement.range(1 to scope(sort)._1, sort)
    
    def createTrackerWithState: StalenessTracker = StalenessTracker.create(sorts, staleMap, scopeMap)

    def afterSubstitution(sortSubstitution: SortSubstitution): StalenessState = {
        val newSorts = sorts map sortSubstitution
        val inverse: Sort => Set[Sort] = sortSubstitution.inverse
        val newScopeMap: Map[Sort, (Int, Boolean)] = {
            for(sort <- newSorts) yield {
                val preImage = inverse(sort)
                val M = preImage.map(scope(_)._1).max
                var s = scope(preImage.head)
                for (item <- preImage) {
                    if( scope(item)._1 == M ) {
                        s = scope(item)
                    }
                }
                sort -> s
            }
        }.toMap
        val newStaleMap: Map[Sort, IndexedSeq[DomainElement]] = {
            for(sort <- newSorts) yield {
                sort -> {
                    val preImage = inverse(sort)
                    val domElems: Set[DomainElement] = for {
                        s <- preImage
                        de <- staleValues(s)
                        de_sub = sortSubstitution.applyDE(de)
                    } yield de_sub
                    domElems.toIndexedSeq.sorted
                }
            }
        }.toMap
        StalenessState(newSorts, newScopeMap, newStaleMap)
    }
}

object StalenessState {
    def apply(
        sorts: Set[Sort],
        scopes: Map[Sort, (Int, Boolean)],
        staleElems: Map[Sort, Seq[DomainElement]]
    ): StalenessState = {
        
        val staleMap = staleElems.map{
            case(sort, seq) => sort -> seq.toIndexedSeq.sorted
        }.toMap
        new StalenessState(sorts, scopes, staleMap)
    }
    
    def apply(
        sorts: Set[Sort],
        scopes: Map[Sort, (Int, Boolean)],
        staleElems: Map[Sort, Set[DomainElement]]
    )(implicit d: DummyImplicit): StalenessState = {

        val staleMap = staleElems.map{
            case(sort, seq) => sort -> seq.toIndexedSeq.sorted
        }.toMap
        new StalenessState(sorts, scopes, staleMap)
    }
}
