package fortress.symmetry

import scala.collection.immutable.Seq

trait HyperGraph[A] {
    
    val vertices: Seq[A]
    val hyperEdges: Set[Set[A]]
    
    private def allPermutationMaps: Seq[Map[A, A]] = {
        val permutationLists: Seq[Seq[A]] = vertices.permutations.toList
        val tupleLists: Seq[Seq[(A, A)]] = permutationLists.map(
            permutationList => vertices.zip(permutationList)
        )
        tupleLists.map(_.toMap)
    }
    
    private def isAutomorphism(permutation: Map[A, A]): Boolean = {
        val powerset: Seq[Set[A]] = vertices.toSet.subsets.toList
        powerset.forall(vertexSubset => {
            val permutationAppliedSet = vertexSubset map permutation
            (hyperEdges contains vertexSubset) == (hyperEdges contains permutationAppliedSet)
        })
    }
    
    def automorphisms: Seq[Map[A, A]] = allPermutationMaps.filter(isAutomorphism)
    
    override def toString: String = {
        "Vertices:   " + vertices.toString + "\n" +
        "Hyperedges: " + hyperEdges.toString
    }
}
