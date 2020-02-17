package fortress.transformers

import fortress.msfol._

import scala.collection.immutable.Seq

import fortress.util.Errors

import util.control.Breaks._

/** Adds symmetry breaking constraints. Only values that are not used are considered
interchangeable (so this needs to be applied before quantifier expansion). Assumes no builtin types. */
class SymBreakTransformer2(scopes: Map[Sort, Int]) extends TheoryTransformer {
    
    def apply(theory: Theory): Theory = {
        val constraints = computeSymmetryBreakingConstraints(theory)
        theory.withAxioms(constraints)
    }
    
    private def computeSymmetryBreakingConstraints(theory: Theory): Set[Term] = {
        val strategy = new SimpleSymBreak(theory, scopes)
        strategy.generatedConstraints
    }
    
    val name: String = "Symmetry Breaking Transformer" 
}

abstract class SymBreakStrategy(theory: Theory, scopes: Map[Sort, Int]) {
    val unbrokenConstants: scala.collection.mutable.Set[AnnotatedVar] =
        scala.collection.mutable.Set.from(theory.constants)
    val unbrokedFunctions: scala.collection.mutable.Set[FuncDecl] = 
        scala.collection.mutable.Set.from(theory.functionDeclarations.filter(f => !f.resultSort.isBuiltin))
    val unbrokenPredicates: scala.collection.mutable.Set[FuncDecl] =
        scala.collection.mutable.Set.from(theory.functionDeclarations.filter(f => f.resultSort == BoolSort))
    
    val unusedValues: scala.collection.mutable.Map[Sort, Seq[DomainElement]] = {
        val usedDomainElements: List[DomainElement] = theory.axioms.map(_.domainElements).fold(Set.empty)((a, b) => a union b).toList
        val mapTuples: Set[(Sort, Seq[DomainElement])] = theory.sorts.filter(!_.isBuiltin).map(sort => {
            val values: Seq[DomainElement] = (1 to scopes(sort)).map(n => DomainElement(n, sort)) diff usedDomainElements
            sort -> values.toList // List for efficient tail
        })
        scala.collection.mutable.Map(mapTuples.toSeq: _*) // Annoying conversion
    }
    
    val usedValues: scala.collection.mutable.Map[Sort, Seq[DomainElement]] = {
        val mapTuples = theory.sorts.filter(!_.isBuiltin).map(sort => sort -> Vector()) // Vector for efficient append
        scala.collection.mutable.Map(mapTuples.toSeq: _*) // Annoying conversion
    }
    
    // Returns whether unused values remain for a sort
    def unusedValuesRemain(sort: Sort): Boolean = unusedValues(sort).nonEmpty
    
    val constraints = new scala.collection.mutable.ListBuffer[Term]
    
    def generateConstantConstraints(sort: Sort): Unit = {
        Errors.precondition(!sort.isBuiltin)
        for(const <- theory.constants if const.sort == sort) {
            if(unusedValuesRemain(sort)) {
                val nextValue = unusedValues(sort).head
                val possibleValues = usedValues(sort) :+ nextValue
                val possibleEqualities = possibleValues.map(v => (const.variable === v))
                if(possibleEqualities.size == 1) {
                    constraints += possibleEqualities.head
                } else {
                    constraints += OrList(possibleEqualities)
                }
                
                // Update used values
                unusedValues(sort) = unusedValues(sort).tail
                usedValues(sort) = usedValues(sort) :+ nextValue
            }
        }
    }
    
    val ArgumentListGenerator = new fortress.util.ArgumentListGenerator(scopes)
    
    def generateDRDConstraints(f: FuncDecl): Unit = {
        Errors.precondition(f.isDomainRangeDistinct)
        Errors.precondition(!f.resultSort.isBuiltin)
        Errors.precondition(!f.argSorts.exists(_.isBuiltin))
        val resultSort = f.resultSort
        // Only the result sort matters as to whether we can do symmetry breaking
        if(unusedValuesRemain(resultSort)) {
            // A Seq[Term] is an argument combination/tuple/list for a function
            val argumentLists: Iterable[Seq[DomainElement]] = ArgumentListGenerator.allArgumentListsOfFunction(f)
            breakable {
                for(argumentList <- argumentLists) {
                    val app = App(f.name, argumentList)
                    
                    val nextValue = unusedValues(resultSort).head
                    println(nextValue)
                    val possibleValues = usedValues(resultSort) :+ nextValue
                    val possibleEqualities = possibleValues.map(v => (app === v))
                    if(possibleEqualities.size == 1) {
                        constraints += possibleEqualities.head
                    } else {
                        constraints += OrList(possibleEqualities)
                    }
                    
                    
                    // Update used values
                    unusedValues(resultSort) = unusedValues(resultSort).tail
                    usedValues(resultSort) = usedValues(resultSort) :+ nextValue
                    
                    // Need to make sure that we record the *arguments* that have been used in formulas too
                    // There should be a more efficient way of doing this
                    for(argument <- argumentList) {
                        val sort = argument.sort
                        unusedValues(sort) = unusedValues(sort) diff Seq(argument)
                        usedValues(sort) = usedValues(sort) :+ argument
                    }
                    
                    // Break early if done
                    if(!unusedValuesRemain(resultSort)) {
                        break
                    }
                }
            }
        }
    }
    
    def generateUnaryPredConstraints(p: FuncDecl): Unit = {
        Errors.precondition(p.resultSort == BoolSort)
        Errors.precondition(p.arity == 1)
        val argSort = p.argSorts.head
        
        val values = unusedValues(argSort).toIndexedSeq
        for {
            i <- 0 to values.size - 2
            j = i + 1
        } {
            constraints += (App(p.name, values(j)) ==> App(p.name, values(i)))
        }
        
        // All the values have now been used for argSort
        unusedValues(argSort) = Seq()
        usedValues(argSort) = (1 to scopes(argSort)).map(n => DomainElement(n, argSort))
    }
    
    def generatedConstraints: Set[Term] = constraints.toSet
}

class SimpleSymBreak(theory: Theory, scopes: Map[Sort, Int]) extends SymBreakStrategy(theory, scopes) {
    // Add constraints for constants
    for(sort <- theory.sorts if !sort.isBuiltin) {
        generateConstantConstraints(sort)
    }
    
    // Add constraints for drd functions
    // There is no rhyme or reason to the functions chosen.
    // This is an area for future research
    for(f <- theory.functionDeclarations if (f.isDomainRangeDistinct && !f.resultSort.isBuiltin)) {
        generateDRDConstraints(f)
    }
    
    // Add constraints for unary predicates
    for(p <- theory.functionDeclarations if (p.resultSort == BoolSort && p.arity == 1)) {
        generateUnaryPredConstraints(p)
    }
    
    
    println("Symmetry breaking constraints")
    println(constraints.toList.mkString("\n"))
    
}
