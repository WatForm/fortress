package fortress.transformers

import fortress.msfol._

import scala.collection.immutable.Seq

import util.control.Breaks._

/** Assumes that the input theory has no domain elements in it, or they all
are interchangeable. Assumes no builtin types. */
class SymBreakTransformer(scopes: Map[Sort, Int]) extends TheoryTransformer {
    
    def apply(theory: Theory): Theory = {
        val constraints = computeSymmetryBreakingConstraints(theory)
        theory.withAxioms(constraints)
    }
    
    def computeSymmetryBreakingConstraints(theory: Theory): Set[Term] = {
        val maxUsedSortVal = scala.collection.mutable.Map[Sort, Int]()
        for(sort <- theory.sorts) {
            maxUsedSortVal(sort) = 0
        }
        
        // Returns ordered list of used values for a sort
        def usedValues(sort: Sort): Seq[DomainElement] =
            (1 to maxUsedSortVal(sort)).map(n => DomainElement(n, sort))
        
        // Returns ordered list of unused values for a sort
        def unusedValues(sort: Sort): Seq[DomainElement] =
            ((maxUsedSortVal(sort) + 1) to scopes(sort)).map(n => DomainElement(n, sort))
        
        // Returns whether unused values remain for a sort
        def unusedValuesRemain(sort: Sort): Boolean = maxUsedSortVal(sort) < scopes(sort)
        
        val constraints = new scala.collection.mutable.ListBuffer[Term]
        
        // Add constraints for constants
        for(const <- theory.constants) {
            val sort = const.sort
            if(unusedValuesRemain(sort)) {
                val nextValue = DomainElement(maxUsedSortVal(sort) + 1, sort)
                val possibleValues = usedValues(sort) :+ nextValue
                val possibleEqualities = possibleValues.map(v => (const.variable === v))
                if(possibleEqualities.size == 1) {
                    constraints += possibleEqualities.head
                } else {
                    constraints += Or(possibleEqualities)
                }
                
                maxUsedSortVal(sort) += 1
            }
        }
        
        val ArgumentListGenerator = new fortress.util.ArgumentListGenerator(scopes)
        
        // Add constraints for drd functions
        // There is no rhyme or reason to the functions chosen.
        // This is an area for future research
        for(f <- theory.functionDeclarations if (f.isDomainRangeDistinct && !f.resultSort.isBuiltin)) {
            val resultSort = f.resultSort
            // Only the result sort matters as to whether we can do symmetry breaking
            if(unusedValuesRemain(resultSort)) {
                // A Seq[Term] is an argument combination/tuple/list for a function
                val argumentLists: Iterable[Seq[DomainElement]] = ArgumentListGenerator.allArgumentListsOfFunction(f)
                breakable {
                    for(argumentList <- argumentLists) {
                        val app = App(f.name, argumentList)
                        
                        val nextValue = DomainElement(maxUsedSortVal(resultSort) + 1, resultSort)
                        val possibleValues = usedValues(resultSort) :+ nextValue
                        val possibleEqualities = possibleValues.map(v => (app === v))
                        if(possibleEqualities.size == 1) {
                            constraints += possibleEqualities.head
                        } else {
                            constraints += Or(possibleEqualities)
                        }
                        
                        maxUsedSortVal(resultSort) += 1
                        
                        // Need to make sure that we record the arguments have been used in formulas
                        // There should be a more efficient way of doing this
                        for(argument <- argumentList) {
                            val sort = argument.sort
                            if(argument.index > maxUsedSortVal(sort)) {
                                maxUsedSortVal(sort) = argument.index
                            }
                        }
                        
                        // Break early if done
                        if(!unusedValuesRemain(resultSort)) {
                            break
                        }
                    }
                }
            }
        }
        
        // Add constraints for unary predicates
        for(p <- theory.functionDeclarations if (p.resultSort == BoolSort && p.arity == 1)) {
            val argSort = p.argSorts.head
            
            val values = unusedValues(argSort).toIndexedSeq
            for {
                i <- 0 to values.size - 2
                j = i + 1
            } {
                constraints += (App(p.name, values(j)) ==> App(p.name, values(i)))
            }
            
            // All the values have now been used for argSort
            maxUsedSortVal(argSort) = scopes(argSort)
        }
        
        println("Symmetry breaking constraints")
        println(constraints.toList.mkString("\n"))
        constraints.toSet
    }
    
    val name: String = "Symmetry Breaking Transformer" 
}
