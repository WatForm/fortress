package fortress.sortinference

import scala.language.implicitConversions
import fortress.msfol._
import fortress.util.Errors
import fortress.util.Maps

import scala.collection.mutable

/**
 * Trait that extends a function from Sort to Sort by applying it to all Sorts appearing 
 * in a term, declaration, signature, theory, etc.
 */
trait GeneralSortSubstitution {
    
    // The function from Sorts to Sorts
    def apply(sort: Sort): Sort
    
    // Apply the Sort function to every appearence of a Sort in a Term.
    def apply(term: Term): Term = term match {
        case Top | Bottom | Var(_)  => term
        case Not(p) => Not(apply(p))
        case AndList(args) => AndList(args map apply)
        case OrList(args) => OrList(args map apply)
        case Distinct(args) => Distinct(args map apply)
        case Implication(p, q) => Implication(apply(p), apply(q))
        case Iff(p, q) => Iff(apply(p), apply(q))
        case Eq(l, r) => Eq(apply(l), apply(r))
        case App(name, args) => App(name, args map apply)
        case Exists(avars, body) => {
            val newVars = avars map {avar => Var(avar.name) of apply(avar.sort)}
            Exists(newVars, apply(body))
        }
        case Forall(avars, body) => {
            val newVars = avars map {avar => Var(avar.name) of apply(avar.sort)}
            Forall(newVars, apply(body))
        }
        case DomainElement(index, sort) => DomainElement(index, apply(sort))
        case EnumValue(_) | BuiltinApp(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => ???
        case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(apply(condition), apply(ifTrue), apply(ifFalse))
    }
    
    // Apply the Sort function to every appearence of a Sort in a FuncDecl.
    def apply(f: FuncDecl): FuncDecl = f match {
        case FuncDecl(name, argSorts, resultSort) => FuncDecl(name, argSorts map apply, apply(resultSort))
    }
    
    // Apply the Sort function to every appearence of a Sort in an AnnotatedVar.
    def apply(avar: AnnotatedVar): AnnotatedVar = avar match {
        case AnnotatedVar(name, sort) => AnnotatedVar(name, apply(sort))
    }
    
    // Apply the Sort function to every appearence of a Sort in a Signature.
    def apply(signature: Signature): Signature = signature match {
        case Signature(sorts, functionDeclarations, constants, enumConstants) => {
            Errors.precondition(enumConstants.isEmpty)
            Signature(
                sorts map apply,
                functionDeclarations map apply,
                constants map apply,
                Map.empty
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
}

object SortSubstitution {
    
    // Given two signatures with the same function and constant names and arities, compute
    // a SortSubstitution that transforms the first signature to the second signature.
    def computeSigMapping(input: Signature, output: Signature): SortSubstitution = {
        val mapping: mutable.Map[Sort, Sort] = mutable.Map.empty
        
        // Constants
        val constantsMapping = for {
            inputConst <- input.constants
            outputConst <- output.queryConstant(inputConst.variable)
        } yield (inputConst.sort -> outputConst.sort)
        
        // Functions
        val functionsMapping = {
            for {
                inputDecl <- input.functionDeclarations
                outputDecl <- output.queryUninterpretedFunction(inputDecl.name)
            } yield {
                val inputSorts = inputDecl.argSorts :+ inputDecl.resultSort
                val outputSorts = outputDecl.argSorts :+ outputDecl.resultSort
                Errors.assertion(inputSorts.size == outputSorts.size)
                inputSorts zip outputSorts
            }
        }.flatten
        
        new SortSubstitution((constantsMapping ++ functionsMapping).toMap)
    }
    
    def identity: SortSubstitution = new SortSubstitution(Map.empty)

    def singleton(substitution: (Sort, Sort)): SortSubstitution = new SortSubstitution(Map(substitution))
}
