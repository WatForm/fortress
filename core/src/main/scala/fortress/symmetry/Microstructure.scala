package fortress.symmetry

import fortress.msfol._
import fortress.util.Errors
import fortress.data._
import fortress.interpretation._
import fortress.operations.TheoryOps._

sealed abstract class Binding
case class ConstBinding(c: AnnotatedVar, value: Value) extends Binding {
    override def toString: String = "<" + c.name + "|" + value.toString + ">"
}
case class FunctionBinding(f: FuncDecl, fnValue: Map[Seq[Value], Value], index: Int) extends Binding {
    def shortName: String = f.name + "_" + index
    override def toString: String = "<" + f.name + "|" + shortName + ">"
}

sealed abstract class ConstOrFunc
case class Const(constant: AnnotatedVar) extends ConstOrFunc
case class Func(functionDeclaration: FuncDecl) extends ConstOrFunc

class MicrostructureComplement(theory: Theory, scopes: Map[Sort, Int]) extends HyperGraph[Binding] {
    
    type HyperEdge = Set[Binding]
    
    def arrangementsWithRepetitions[T](sequence: List[T], length: Int): List[List[T]] = {
        if (length == 0) List(List.empty)
        else {
            for {
                item  <- sequence.toList
                smallerArrangement <- arrangementsWithRepetitions(sequence, length - 1)
            } yield (item :: smallerArrangement)
        }
    }
    
    def possibleConstBindings(c: AnnotatedVar): Seq[ConstBinding] =
        for(i <- 1 to scopes(c.sort)) yield ConstBinding(c, DomainElement(i, c.sort))
    
    val possibleConstBindingsMap: Map[AnnotatedVar, Seq[ConstBinding]] = (
        for (c <- theory.constants) yield (c, possibleConstBindings(c))
    ).toMap
        
    def possibleFunctionBindings(f: FuncDecl): Seq[FunctionBinding] = {
        val possibleRangeValues: Seq[Value] = f.resultSort match {
            case BoolSort => Seq(Top, Bottom)
            case SortConst(_) => DomainElement.range(1 to scopes(f.resultSort), f.resultSort)
            case _ => ???
        }
            
        //  f: A_1 x ... x A_n -> B
        // and each A_i has generated domain D_i
        // get the list [D_1, ..., D_n]
        val seqOfDomainSeqs: IndexedSeq[IndexedSeq[DomainElement]] = f.argSorts.toIndexedSeq.map (sort => {
            DomainElement.range(1 to scopes(sort), sort)
        })
        
        // Take the product D_1 x ... x D_n
        val argumentLists: Iterable[Seq[DomainElement]] = new CartesianSeqProduct[DomainElement](seqOfDomainSeqs)
        val domainSize = argumentLists.size
        
        // Compute possible output sequences
        val possibleOutputSequences: Seq[Seq[Value]] = arrangementsWithRepetitions[Value](possibleRangeValues.toList, domainSize)
        
        var index = 0
        for(outputSequence <- possibleOutputSequences) yield {
            Errors.Internal.assertion(argumentLists.size == outputSequence.size)
            index += 1
            val tuples: List[(Seq[DomainElement], Value)] = argumentLists.toList zip outputSequence
            
            FunctionBinding(f, tuples.toMap, index)
        }
    }
    
    override val vertices: Seq[Binding] = {
        val _vertices = new scala.collection.mutable.ListBuffer[Binding]
        for(c <- theory.constants; binding <- possibleConstBindings(c)) {
            _vertices += binding
        }
        for(f <- theory.functionDeclarations; binding <- possibleFunctionBindings(f)){
            _vertices += binding
        }
        _vertices.toList
    }
    
    val consistencyEdges: Seq[HyperEdge] = {
        val _consistencyEdges = new scala.collection.mutable.ListBuffer[Set[Binding]]
        
        for(c <- theory.constants) {
            val _possibleBindings = possibleConstBindings(c)
            for(x <- _possibleBindings; y <- _possibleBindings if x != y) {
                _consistencyEdges += Set(x, y)
            }
        }
        
        for(f <- theory.functionDeclarations) {
            val _possibleBindings = possibleFunctionBindings(f)
            for(x <- _possibleBindings; y <- _possibleBindings if x != y) {
                _consistencyEdges += Set(x, y)
            }
        }
        _consistencyEdges.toList
    }
    
    val possibleFunctionBindingsMap: Map[FuncDecl, Seq[FunctionBinding]] = (
        for (f <- theory.functionDeclarations) yield (f, possibleFunctionBindings(f))
    ).toMap
    
    // This is not efficient
    // Would be better to generate all possible interpretations only for the needed subset
    // of vertices that occur in the formula
    
    lazy val allPossibleInterpretations: Seq[Interpretation] = {
        // Always the same interpretation for sorts
        val sortInterpretations: Map[Sort, Seq[Value]] = theory.sorts.filter(!_.isBuiltin).map(sort => {
            val values: Seq[Value] = DomainElement.range(1 to scopes(sort), sort)
            (sort, values)
        }).toMap

        val possibleInterpretationsConstants: Seq[Map[AnnotatedVar, Value]] = {
            // Constants c1, ..., ck
            // Each has a sequence of possible bindings Ai
            // Take the cartesian product of the lists A1 x ... Ak
            val Ais: IndexedSeq[IndexedSeq[ConstBinding]] = theory.constants.map(possibleConstBindingsMap(_).toIndexedSeq).toIndexedSeq
            val product = new CartesianSeqProduct[ConstBinding](Ais)
            // Each element of this product gives an interpretation
            for(bindingSeq <- product.toList) yield {
                bindingSeq.map(binding => (binding.c, binding.value)).toMap
            }
        }
        val possibleInterpretationsFunctions: Seq[Map[FuncDecl, Map[Seq[Value], Value]]] = {
            // Functions g1, ..., gk
            // Each has a sequence of possible bindings Ai
            // Take the cartesian product of the lists A1 x ... Ak
            val Ais: IndexedSeq[IndexedSeq[FunctionBinding]] = theory.functionDeclarations.map(possibleFunctionBindingsMap(_).toIndexedSeq).toIndexedSeq
            val product = new CartesianSeqProduct[FunctionBinding](Ais)
            // Each element of this product gives an interpretation
            for(bindingSeq <- product.toList) yield {
                val interp = bindingSeq.map(binding => (binding.f, binding.fnValue)).toMap
                interp
            }
        }
        for(
            interpretationForConstants <- possibleInterpretationsConstants;
            interpretationForFunctions <- possibleInterpretationsFunctions
        ) yield
            new BasicInterpretation(
                sortInterpretations,
                interpretationForConstants,
                interpretationForFunctions,
                // TODO: modification is needed
                functionDefinitions = Set.empty
            )
    }
    
    def lookupIndex(f: FuncDecl, fnValue: Map[Seq[Value], Value]): Int =
        possibleFunctionBindingsMap(f).find(_.fnValue == fnValue).get.index
    
    val constraintEdges: Map[Term, Set[HyperEdge]] = {
        val mutMap = scala.collection.mutable.Map.empty[Term, Set[HyperEdge]]
        for(axiom <- theory.axioms) {
            val hyperEdgesForAxiom = new scala.collection.mutable.ListBuffer[HyperEdge]
            
            val constSymbolsOfAxiom: Set[AnnotatedVar] =  {
                val constantsIn = fortress.operations.RecursiveAccumulator.constantsIn(axiom)
                constantsIn.map(x => theory.signature.getAnnotatedVarOfConstant(Var(x)).get)
            }
            val funcSymbolsOfAxiom: Set[FuncDecl] = {
                val functionsIn = fortress.operations.RecursiveAccumulator.functionsIn(axiom)
                functionsIn.map(theory.signature.queryFunctionDeclaration(_).get)
            }
            
            // Make a new theory containing only this one axiom to see if this axiom is broken
            val restrictedTheory = Theory.mkTheoryWithSignature(theory.signature).withAxiom(axiom)
            
            // Check each assignment if it is valid
            for(interpretation <- allPossibleInterpretations) {
                if (! (restrictedTheory verifyInterpretation interpretation) ) {
                    // Add hyperedge
                    // take only part that occurs in this axiom
                    val relevantConstBindings: Set[ConstBinding] = {
                        val relevantMappings: Map[AnnotatedVar, Value] = interpretation.constantInterpretations.filter(constSymbolsOfAxiom contains _._1)
                        relevantMappings.map(tuple => ConstBinding(tuple._1, tuple._2)).toSet
                    }
                    val relevantFunctionBindings: Set[FunctionBinding] = {
                        // What about index?
                        // Inefficient solution
                        val relevantMappings: Map[FuncDecl, Map[Seq[Value], Value]] = interpretation.functionInterpretations.filter(funcSymbolsOfAxiom contains _._1)
                        relevantMappings.map{ case(f, fnValue) => {
                            FunctionBinding(f, fnValue, lookupIndex(f, fnValue))
                        }}.toSet
                    }
                    hyperEdgesForAxiom += relevantConstBindings ++ relevantFunctionBindings
                }
            }
            mutMap += (axiom -> hyperEdgesForAxiom.toSet)
        }
        mutMap.toMap
    }
    
    override val hyperEdges: Set[HyperEdge] =
        consistencyEdges.toSet ++ constraintEdges.values.flatten.toSet
    
    override def toString: String = {
        val builder = new scala.collection.mutable.StringBuilder
        builder ++=  "Vertices:   " + vertices.mkString(" ") + "\n"
        builder ++= "Consistency hyperedges: " + consistencyEdges.toSet.mkString(" ") + "\n\n"
        builder ++= "Constraint hyperedges: " + "\n"
        for(axiom <- theory.axioms) {
            builder ++= "Axiom: " + axiom.toString + "\n"
            builder ++= "Edges: " + constraintEdges(axiom).mkString(" ") + "\n\n"
        }
        
        if(theory.functionDeclarations.nonEmpty) {
            builder ++= "Functions:"
        }
        
        for(f <- theory.functionDeclarations) {
            builder ++= "\n" + f.toString + "\n"
            for(functionBinding <- possibleFunctionBindingsMap(f)) {
                builder ++= functionBinding.shortName + ": " + functionBinding.fnValue.toString + "\n"
            }
        }
        
        builder.toString
    }
}
