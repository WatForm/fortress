package fortress.sortinference

import scala.language.implicitConversions
import fortress.msfol._
import fortress.util.Errors
import fortress.util.Errors2
import fortress.util.Maps

import scala.collection.mutable
import fortress.interpretation.FunctionInterpretation

/**
 * Trait that extends a function from Sort to Sort by applying it to all Sorts appearing 
 * in a term, declaration, signature, theory, etc.
 */
trait GeneralSortSubstitution {
    
    // The function from Sorts to Sorts
    def apply(sort: Sort): Sort
    
    // Apply the Sort function to every appearence of a Sort in a Term.
    def apply(term: Term): Term = term match {
        // Function Interpretations assume if the input is a Value the output is also a Value
        case Top | Bottom | Var(_) | EnumValue(_) | IntegerLiteral(_) | BitVectorLiteral(_, _) => term
        case Not(p) => Not(apply(p))
        case AndList(args) => AndList(args map apply)
        case OrList(args) => OrList(args map apply)
        case Distinct(args) => Distinct(args map apply)
        case Implication(p, q) => Implication(apply(p), apply(q))
        case Iff(p, q) => Iff(apply(p), apply(q))
        case Eq(l, r) => Eq(apply(l), apply(r))
        case App(name, args) => App(name, args map apply)
        case Closure(name, arg1, arg2, args) => Closure(name, apply(arg1), apply(arg2), args map apply)
        case ReflexiveClosure(name, arg1, arg2, args) => ReflexiveClosure(name, apply(arg1), apply(arg2), args map apply)
        case Exists(avars, body) => {
            val newVars = avars map {avar => Var(avar.name) of apply(avar.sort)}
            Exists(newVars, apply(body))
        }
        case Forall(avars, body) => {
            val newVars = avars map {avar => Var(avar.name) of apply(avar.sort)}
            Forall(newVars, apply(body))
        }
        case DomainElement(index, sort) => DomainElement(index, apply(sort))
        case BuiltinApp(name, args) => BuiltinApp(name, args map apply)
        case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(apply(condition), apply(ifTrue), apply(ifFalse))
    }
    
    // Apply the Sort function to every appearence of a Sort in a FuncDecl.
    def apply(f: FuncDecl): FuncDecl = f match {
        case FuncDecl(name, argSorts, resultSort) => FuncDecl(name, argSorts map apply, apply(resultSort))
    }

    def apply(fd: FunctionDefinition): FunctionDefinition = fd match {
        case FunctionDefinition(name, argSortedVar, resultSort, body) => FunctionDefinition(name, argSortedVar map apply, apply(resultSort), apply(body))
    }
    
    // Apply the Sort function to every appearence of a Sort in an AnnotatedVar.
    def apply(avar: AnnotatedVar): AnnotatedVar = avar match {
        case AnnotatedVar(name, sort) => AnnotatedVar(name, apply(sort))
    }

    def apply(cDef: ConstantDefinition): ConstantDefinition = ConstantDefinition(
        apply(cDef.avar),
        apply(cDef.body)
    )
    
    // Apply the Sort function to every appearence of a Sort in a Signature.
    def apply(signature: Signature): Signature = signature match {
        case Signature(sorts, functionDeclarations, functionDefinitions, constantDeclarations, constantDefinitions, enumConstants) => {
            Signature(
                sorts map apply,
                functionDeclarations map apply,
                functionDefinitions map apply,
                constantDeclarations map apply,
                constantDefinitions map apply,
                enumConstants.map{case(sort, enumConstants) => (apply(sort), enumConstants)}
            )
        }
    }
    
    // Apply the Sort function to every appearence of a Sort in a Theory.
    def apply(theory: Theory): Theory = {
        Theory.mkTheoryWithSignature(apply(theory.signature))
            .withAxioms(theory.axioms map apply)
    }
    
    // Apply the Sort function to every appearence of a Sort in a Value.
    def applyValue(value: Value): Value = value match {
        case Top | Bottom => value
        case EnumValue(_) | BitVectorLiteral(_, _) | IntegerLiteral(_) => ???
        case DomainElement(index, sort) => DomainElement(index, apply(sort))
    }

    // Apply the Sort function to every appearence of a Sort in a Value.
    // We keep integers the same for FunctionInterpretations. 
    // We assume Ints are not really used in sort substitutions and enums are not present
    def applyValueKeepInts(value: Value): Value = value match {
        case Top | Bottom => value
        case EnumValue(_) => ???
        case BitVectorLiteral(_, _) | IntegerLiteral(_) => value
        case DomainElement(index, sort) => DomainElement(index, apply(sort))
    }

    def applyDE(de: DomainElement): DomainElement = de match {
        case DomainElement(index, sort) => DomainElement(index, apply(sort))
    }

    def apply(rangeRestriction: RangeRestriction): RangeRestriction = rangeRestriction match {
        case RangeRestriction(term, values) => RangeRestriction(apply(term), values map applyDE)
    }

    def apply(equation: Equation): Equation = equation match {
        case Equation(s, t) => Equation(apply(s), apply(t))
    }
    
}

object GeneralSortSubstitution {
    // Because of type erasure we can't extend both Function[Sort, Sort] and Function[Term, Term]
    // so we use delegation and implicits to simulate this
    
    implicit def asSortFunction(sigma: GeneralSortSubstitution): Sort => Sort = (sort => sigma(sort))
    
    implicit def asTermFunction(sigma: GeneralSortSubstitution): Term => Term = (term => sigma(term))

    implicit def asDeclFunction(sigma: GeneralSortSubstitution): FuncDecl => FuncDecl = (f => sigma(f))
}

class SortSubstitution(_mapping: Map[Sort, Sort]) extends GeneralSortSubstitution {

    private val mapping: Map[Sort, Sort] = Maps.removeFixedPoints(_mapping)
    
    override def apply(sort: Sort): Sort = mapping.getOrElse(sort, sort)
    
    override def toString: String = mapping.toString
    
    def inverse: Sort => Set[Sort] = {
        val tuplesByValue: Map[Sort, Seq[(Sort, Sort)]] = mapping.toSeq.groupBy(_._2)
        val inverseMapping: Map[Sort, Set[Sort]] = tuplesByValue.map {
            case (sort, seq) => (sort, seq.map(_._1).toSet)
        }.toMap
        (sort: Sort) => inverseMapping.getOrElse(sort, Set(sort))
    }
    
    def isBijectiveRenaming: Boolean = Maps.isInjective(mapping)
    
    def isIdentity: Boolean = Maps.isIdentity(mapping)

    def domain: Set[Sort] = mapping.keySet

    def compose(other: SortSubstitution): SortSubstitution = {
        val sigma = this
        val gamma = other
        // Sigma compose Gamma
        val kind1 = for((x, t) <- gamma.mapping) yield (x -> sigma(t))
        val kind2 = for((x, t) <- sigma.mapping if !(gamma.domain contains x)) yield (x -> t)
        new SortSubstitution(kind1 ++ kind2)
    }

    def union(other: SortSubstitution): SortSubstitution = {
        new SortSubstitution(Maps.merge(mapping, other.mapping))
    }
}

object SortSubstitution {
    
    // Given two signatures with the same function and constant names and arities, compute
    // a SortSubstitution that transforms the first signature to the second signature.
    def computeSigMapping(input: Signature, output: Signature): SortSubstitution = {
        val mapping: mutable.Map[Sort, Sort] = mutable.Map.empty
        
        // Constants
        val constantDeclsMapping = for {
            inputConst <- input.constantDeclarations
            outputConst <- output.queryConstantDeclaration(inputConst.variable)
        } yield (inputConst.sort -> outputConst.sort)

        val constantDefnsMapping = for {
            inputConst <- input.constantDefinitions
            outputConst <- output.queryConstantDefinition(inputConst.variable)
        } yield (inputConst.sort -> outputConst.sort)
        
        // Functions
        val functionsMapping = {
            for {
                inputDecl <- input.functionDeclarations
                outputDecl <- output.queryFunctionDeclaration(inputDecl.name)
            } yield {
                val inputSorts = inputDecl.argSorts :+ inputDecl.resultSort
                val outputSorts = outputDecl.argSorts :+ outputDecl.resultSort
                Errors.Internal.assertion(inputSorts.size == outputSorts.size)
                inputSorts zip outputSorts
            }
        }.flatten
        
        new SortSubstitution((constantDeclsMapping ++ constantDefnsMapping ++  functionsMapping).toMap)
    }

    // Takes two terms that have the same shape modulo sorts, and produces a substitution
    // which turns the input term into the output term
    def computeTermMapping(input: Term, output: Term): SortSubstitution = {
        def recur(input: Term, output: Term): Map[Sort, Sort] = (input, output) match {
            case (Top, Top) => Map()
            case (Bottom, Bottom) => Map()
            case (Var(_), Var(_)) => Map()
            case (Not(p), Not(q)) => recur(p, q)
            case (AndList(args1), AndList(args2)) => recurs(args1, args2)
            case (OrList(args1), OrList(args2)) => recurs(args1, args2)
            case (Distinct(args1), Distinct(args2)) => recurs(args1, args2)
            case (Implication(p1, q1), Implication(p2, q2)) => Maps.merge(recur(p1, p2), recur(q1, q2))
            case (Iff(p1, q1), Iff(p2, q2)) => Maps.merge(recur(p1, p2), recur(q1, q2))
            case (Eq(p1, q1), Eq(p2, q2)) => Maps.merge(recur(p1, p2), recur(q1, q2))
            case (App(f1, args1), App(f2, args2)) => recurs(args1, args2)
            case (Exists(avars1, body1), Exists(avars2, body2)) => {
                val tuples = for {
                    (AnnotatedVar(_, sort1), AnnotatedVar(_, sort2)) <- avars1 zip avars2
                } yield (sort1 -> sort2)
                Maps.merge(tuples.toMap, recur(body1, body2))
            }
            case (Forall(avars1, body1), Forall(avars2, body2)) => {
                val tuples = for {
                    (AnnotatedVar(_, sort1), AnnotatedVar(_, sort2)) <- avars1 zip avars2
                } yield (sort1 -> sort2)
                Maps.merge(tuples.toMap, recur(body1, body2))
            }
            case (DomainElement(_, s1), DomainElement(_, s2)) => Map(s1 -> s2)
            case (EnumValue(_), EnumValue(_)) => Map()
            case (IfThenElse(c1, t1, f1), IfThenElse(c2, t2, f2)) => recurs(Seq(c1, t1, f1), Seq(c2, t2, f2))
            case (IntegerLiteral(_), IntegerLiteral(_)) => Map()
            case (BitVectorLiteral(_, _), BitVectorLiteral(_, _)) => Map()
            case (BuiltinApp(f1, args1), BuiltinApp(f2, args2)) => recurs(args1, args2)
            case (Closure(f1, args1a, args1b, fixedArgs1), Closure(f2, args2a, args2b, fixedArgs2)) => {
                val mapA = recur(args1a, args2a)
                val mapB = recur(args1b, args2b)
                val mapFixed = recurs(fixedArgs1, fixedArgs2)
                Maps.merge(Maps.merge(mapA, mapB), mapFixed)
            }
            case (ReflexiveClosure(f1, args1a, args1b, fixedArgs1), ReflexiveClosure(f2, args2a, args2b, fixedArgs2)) => {
                val mapA = recur(args1a, args2a)
                val mapB = recur(args1b, args2b)
                val mapFixed = recurs(fixedArgs1, fixedArgs2)
                Maps.merge(Maps.merge(mapA, mapB), mapFixed)
            }
            case _ => ???
        }

        def recurs(inputs: Seq[Term], outputs: Seq[Term]): Map[Sort, Sort] = (inputs zip outputs).foldLeft(Map.empty[Sort, Sort])((map, nextPair) => Maps.merge(map, recur(nextPair._1, nextPair._2)))

        new SortSubstitution(recur(input, output))
    }
    
    def identity: SortSubstitution = new SortSubstitution(Map.empty)

    def singleton(substitution: (Sort, Sort)): SortSubstitution = new SortSubstitution(Map(substitution))
}

/**
  * A Sort Substitution where values can be specified to be substituted as well
  *
  * @param sortMapping
  * @param valueMapping
  */
class ValuedSortSubstitution(sortMapping: Map[Sort,Sort], valueMapping: Map[Value,Value]) extends SortSubstitution(sortMapping){
    override def applyValue(value: Value): Value = {
        if (valueMapping isDefinedAt value)
        {
            valueMapping(value)
        } else {
            super.applyValue(value)
        }
    }

    override def apply(term: Term): Term = term match {
        case Var(_)  => term
        case Not(p) => Not(apply(p))
        case AndList(args) => AndList(args map apply)
        case OrList(args) => OrList(args map apply)
        case Distinct(args) => Distinct(args map apply)
        case Implication(p, q) => Implication(apply(p), apply(q))
        case Iff(p, q) => Iff(apply(p), apply(q))
        case Eq(l, r) => Eq(apply(l), apply(r))
        case App(name, args) => App(name, args map apply)
        case Closure(name, arg1, arg2, args) => Closure(name, apply(arg1), apply(arg2), args map apply)
        case ReflexiveClosure(name, arg1, arg2, args) => ReflexiveClosure(name, apply(arg1), apply(arg2), args map apply)
        case Exists(avars, body) => {
            val newVars = avars map {avar => Var(avar.name) of apply(avar.sort)}
            Exists(newVars, apply(body))
        }
        case Forall(avars, body) => {
            val newVars = avars map {avar => Var(avar.name) of apply(avar.sort)}
            Forall(newVars, apply(body))
        }
        case BuiltinApp(_, _) => ???
        case v: Value => applyValue(v)
        case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(apply(condition), apply(ifTrue), apply(ifFalse))
    }

    override def apply(fd: FunctionDefinition): FunctionDefinition = fd match {case FunctionDefinition(name, argSortedVars, resultSort, body) => {
        // Just apply to everything here
        val newArgSorts = argSortedVars map apply
        val newResultSort = apply(resultSort)
        val newBody = apply(body)

        FunctionDefinition(name, newArgSorts, newResultSort, newBody)
    }}
}

// A substitution that always assigns a unique new sort to every sort it sees.
// Even if it sees the same sort twice, it will spit out a different sort
class FreshCountingSubstitution extends GeneralSortSubstitution {
    var index = 0
    def freshInt(): Int = {
        val temp = index
        index += 1
        temp
    }

    def sortVar(index: Int): SortConst = SortConst("S" + index.toString)
        
    def sortVarAsInt(s: SortConst): Int = s.name.tail.toInt
    
    override def apply(sort: Sort) = sort match {
        case SortConst(_) => sortVar(freshInt())
        case sort => sort
    }
}