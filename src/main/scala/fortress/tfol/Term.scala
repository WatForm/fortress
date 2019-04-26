package fortress.tfol

import fortress.util.Errors
import fortress.tfol.operations._
import fortress.data._
import fortress.outputs._
import fortress.sexpr._
import scala.collection.JavaConverters._
import scala.annotation.varargs // So we can call Scala varargs methods from Java
import scala.collection.immutable.Seq // Default to immutable Seqs

/** Representation of a syntactic Term. */
sealed abstract class Term {
    def accept[T](visitor: TermVisitor[T]): T
    
    /** Returns the set of Vars that appear unquantified in this term.
      * This only looks at syntax without respect to a given signature,
      * so it could also include what are intended to be constants.
      */ 
    def freeVarConstSymbols: Set[Var] = FreeVariables(this)
    def freeVarConstSymbolsJava: java.util.Set[Var] = FreeVariables(this).asJava
    
    /** Returns the set of free variables of this term with respect
      * to the given signature. Constants of the signature are not included.
      */ 
    def freeVars(signature: Signature): java.util.Set[Var] = {
        val constants = signature.constants.map(_.variable)
        (FreeVariables(this) diff constants).asJava
    }
    
    /** Given a signature, typechecks the term with respect to the signature.
      * Returns a TypeCheckResult containing the type of the term, AND a new term
      * that is equal to the old term but with instances of Eq replaced with Iff
      * when comparing Bool types. Such a term is called "sanitized".
      */
    def typeCheck(signature: Signature): TypeCheckResult =
        TypeChecker.typeCheck(signature, this)
    
    /** Returns the negation normal form version of this term.
      * The term must be sanitized to call this method.
      */
    def nnf: Term = NegationNormalizer(this)
    
    /** Returns an SExpr representing this term as it would appear in SMT-LIB. */
    def toSmtExpr: SExpr = new SmtExprVisitor().visit(this)
    
    /** Returns a term that is alpha-equivalent to this one but whose quantified
      * variables are instead De Bruijn indices. Note that these indices are prefixed
      * by an underscore to make it clearer (e.g. the first quantified variable is "_1")
      */
    def deBruijn: Term = new DeBruijnConverter().convert(this)
    
    /** Returns true iff the other term is alpha-equivalen to this term. */
    def alphaEquivalent(other: Term): Boolean = this.deBruijn == other.deBruijn
    
    def substitute(toSub: Var, subWith: Term, nameGenerator: NameGenerator): Term =
        Substituter(toSub, subWith, this, nameGenerator)
    
    def substitute(toSub: Var, subWith: Term): Term =
        substitute(toSub, subWith, new SubIntNameGenerator(java.util.Set.of[String], 0))
    
    /** Does not account for variable capture.
      * If in doubt do not use this function.
      */
    def recklessSubstitute(substitutions: Map[Var, Term]): Term =
        RecklessSubstituter(substitutions, this)
    
    def recklessSubstituteJava(substitutions: java.util.Map[Var, Term]): Term =
        RecklessSubstituter(substitutions.asScala.toMap, this)
    
    def recklessUnivInstantiate(typeInstantiations: java.util.Map[Type, java.util.List[Term]]): Term =
        new RecklessUnivInstantiationVisitor(typeInstantiations).visit(this)
    
    def simplify: Term = Simplifier(this)
    
    def eliminateDomainElements = DomainElementEliminator(this)
    
    /** Returns the set of all symbol names used in the term, including:
      * free variables and constants, bound variables (even those that aren't used),
      * function names, and type names that appear on variable bindings.
      */
    def allSymbols: Set[String] = AllSymbols(this)
    def allSymbolsJava: java.util.Set[String] = allSymbols.asJava
    
    // Be aware if you chain this method together, you will get several nested AndLists
    def and(other: Term): Term = AndList(Seq(this, other))
    // Be aware if you chain this method together, you will get several nested OrLists
    def or(other: Term): Term = OrList(Seq(this, other))
    def ==>(other: Term): Term = Implication(this, other)
    def ===(other: Term): Term = Eq(this, other)
}

/** Term that represents True. */
case class Top() extends Term {
    override def toString: String = "true"
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitTop(this)
}

/** Term that represents Bottom. */
case class Bottom() extends Term {
    override def toString: String = "false"
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitBottom(this)
}

/** Term that represents a variable (including prime propositions).
  * Variables and constants are treated as syntactically indistinguishable.
  * Whether it is treated as a variable or constant depends on the context
  * in which it is used (e.g. a signature or quantifier binding).
  */
case class Var(name: String) extends Term {
    Errors.precondition(name.length() > 0, "Cannot create variable with empty name")
    Errors.precondition(! Names.isIllegal(name), "Illegal variable name " + name)
    
    override def toString: String = name
    def getName: String = name
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitVar(this)
    
    /** Returns an AnnotatedVar that represents this variable annotated with
      * with a Type.
      */
    def of(sort: Type) = AnnotatedVar(this, sort)
}

/** Represents a variable together with a Type annotation.
  * Used when quantifying a variable, or when declaring a Var to be a constant
  * of a given Type.
  * AnnotatedVar is not a subclass of Term.
  * Inside a Term it is only possible (and required) to annotate a Var when
  * a quantifier declares it bound.
  */
case class AnnotatedVar(variable: Var, sort: Type) {
    def getVar: Var = variable
    def getType: Type = sort
    def getName: String = variable.name
    
    override def toString: String = variable.toString + ": " + sort.toString
}

/** Represents a negation. */
case class Not(body: Term) extends Term {
    def getBody: Term = body
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitNot(this)
    def mapBody(mapping: Term => Term): Term = Not(mapping(body))
    
    override def toString: String = "~" + body.toString
}

/** Represents a conjunction. */
case class AndList private (arguments: Seq[Term]) extends Term {
    Errors.precondition(arguments.size >= 2)
    
    def getArguments: java.util.List[Term] = arguments.asJava
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitAndList(this)
    def mapArguments(mapping: Term => Term): Term =
        AndList(arguments.map(mapping))
    
    override def toString: String = "And(" + arguments.mkString(", ") + ")"
}

object AndList {
    def apply(args: Term*): Term = AndList(args.toList)
}

object And {
    def apply(args: Term*): Term = AndList(args.toList)
    def apply(args: Seq[Term]) = if(args.size == 1) args(0) else AndList(args)
}

/** Represents a disjunction. */
case class OrList private (arguments: Seq[Term]) extends Term {
    Errors.precondition(arguments.size >= 2)
    
    def getArguments: java.util.List[Term] = arguments.asJava
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitOrList(this)
    def mapArguments(mapping: Term => Term): Term =
        OrList(arguments.map(mapping))
    
    override def toString: String = "Or(" + arguments.mkString(", ") + ")"
}

object OrList {
    def apply(args: Term*): Term = OrList(args.toList)
}

object Or {
    def apply(args: Term*): Term = Or(args.toList)
    def apply(args: Seq[Term]) = if(args.size == 1) args(0) else OrList(args)
}

/** Represents a formula signifying whether its arguments have distinct values. */
case class Distinct(arguments: Seq[Term]) extends Term {
    Errors.precondition(arguments.size >= 2)
    
    def getArguments: java.util.List[Term] = arguments.asJava
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitDistinct(this)
    def mapArguments(mapping: Term => Term): Term =
        Distinct(arguments.map(mapping))
    
    def asPairwiseNotEquals: Term = {
        // TODO update this to be scala code
        val pairs: java.util.List[Term] = new java.util.ArrayList[Term]()
        var i = 0
        arguments.foreach (ti => {
            i += 1
            var j = 0
            arguments.foreach (tj => {
                j += 1 ;
                if (i < j) pairs.add(Not(Eq(ti, tj)))
            })
        })
        val n = arguments.size
        Errors.assertion(pairs.size() == (n*(n - 1) / 2), "" + n + " terms, but somehow generated " + pairs.size() + " pairs")
        Term.mkAnd(pairs)
    }
    
    override def toString: String = "Distinct(" + arguments.mkString(", ") + ")"
}

object Distinct {
    def apply(arguments: Term*): Term = Distinct(arguments.toList)
}

/** Represents an implication. */
case class Implication(left: Term, right: Term) extends Term {
    def getLeft: Term = left
    def getRight: Term = right
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitImplication(this)
    def mapArguments(mapping: Term => Term): Term =
        Implication(mapping(left), mapping(right))
    
    override def toString: String = left.toString + " => " + right.toString
}

/** Represents a bi-equivalence. */
case class Iff(left: Term, right: Term) extends Term {
    def getLeft: Term = left
    def getRight: Term = right
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitIff(this)
    def mapArguments(mapping: Term => Term): Term =
        Iff(mapping(left), mapping(right))
    
    override def toString: String = left.toString + " <=> " + right.toString
}

/** Represents an equality. */
case class Eq(left: Term, right: Term) extends Term {
    def getLeft: Term = left
    def getRight: Term = right
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitEq(this)
    def mapArguments(mapping: Term => Term): Term =
        Eq(mapping(left), mapping(right))
        
    override def toString: String = left.toString + " = " + right.toString
}

/** Represents a function or predicate application. */
case class App(functionName: String, arguments: Seq[Term]) extends Term {
    Errors.precondition(functionName.length >= 1, "Empty function name")
    Errors.precondition(arguments.size >= 1, "Nullary function application " + functionName + " should be a Var")
    
    def getArguments: java.util.List[Term] = arguments.asJava
    def getFunctionName: String = functionName
    override def accept[T](visitor: TermVisitor[T]): T  = visitor.visitApp(this)
    def mapArguments(mapping: Term => Term): Term =
        App(functionName, arguments.map(mapping))
    
    override def toString: String = functionName + "(" + arguments.mkString(", ") + ")"
}

object App {
    def apply(functionName: String, arguments: Term*): App = App(functionName, arguments.toList)
}

sealed abstract class Quantifier extends Term {
    def getVars: java.util.List[AnnotatedVar]
    def getBody: Term
    def mapBody(mapping: Term => Term): Term
}

/** Represents an existentially quantified Term. */
case class Exists(vars: Seq[AnnotatedVar], body: Term) extends Quantifier {
    Errors.precondition(vars.size >= 1, "Quantifier must bind at least one variable");
    // Check variables distinct
    Errors.precondition(vars.map(av => av.getName).toSet.size == vars.size, "Duplicate variable name in quantifier")
    
    def getVars: java.util.List[AnnotatedVar] = vars.asJava
    def getBody: Term = body
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitExists(this)
    def mapBody(mapping: Term => Term): Term = Exists(vars, mapping(body))
    
    override def toString: String = "exists " + vars.mkString(", ") + " . " + body.toString
}

object Exists {
    def apply(variable: AnnotatedVar, body: Term): Exists = Exists(Seq(variable), body)
}

/** Represents a universally quantified Term. */
case class Forall(vars: Seq[AnnotatedVar], body: Term) extends Quantifier {
    Errors.precondition(vars.size >= 1, "Quantifier must bind at least one variable")
    // Check variables distinct
    Errors.precondition(vars.map(av => av.getName).toSet.size == vars.size, "Duplicate variable name in quantifier")
    
    def getVars: java.util.List[AnnotatedVar] = vars.asJava
    def getBody: Term = body
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitForall(this)
    def mapBody(mapping: Term => Term): Term = Forall(vars, mapping(body))
    
    override def toString: String = "exists " + vars.mkString(", ") + " . " + body.toString
}

object Forall {
    def apply(variable: AnnotatedVar, body: Term): Forall = Forall(Seq(variable), body)
}

/** Represents an indexed domain element.
  * For example, DomainElement(2, A) represents the domain element at index 2
  * for sort A, written as 2A.
  * DomainElements are indexed starting with 1.*/
case class DomainElement(index: Int, sort: Type) extends Term {
    Errors.precondition(index >= 1)
    
    def getIndex: Int = index
    def getType: Type = sort
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitDomainElement(this)
    
    // TODO need to restrict any other code from using this naming convention
    val asSmtConstant = Var("@" + index.toString + sort.toString)
}

/** Represents an application/membership test of the transitive closure of a predicate/relation.
  * For example, TC(P, x, y) represents the truth value of whether (x, y) is a member of the 
  * the transitive closure of P. */
case class TC(relationName: String, arg1: Term, arg2: Term) extends Term {     
    Errors.precondition(relationName.length >= 1, "Empty relation name in transitive closure")
    
    def mkApp(functionName: String): App = App(functionName, arg1, arg2)
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitTC(this)     
    def mapBody(mapping: Term => Term) = TC(relationName, mapping(arg1), mapping(arg2))     
}

case class IntegerLiteral(value: Int) extends Term {
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitIntegerLiteral(this)
}

case class BitVectorLiteral(value: Int, bitWidth: Int) extends Term {
    Errors.precondition(bitWidth > 0)
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitBitVectorLiteral(this)
}

/** Companion object for Term. */
object Term {
    /** Returns a Term representing Top/Verum */
    def mkTop: Term = Top()
    
    /** Returns a Term representing Bottom/Falsum */
    def mkBottom: Term = Bottom()
    
    /** Returns a Term representing the variable (or constant, depending on the
      * context in which it is used) with the given name.
      */
    def mkVar(name: String): Var = Var(name)
    
    /** Returns a Term representing the conjunction of the given terms. One or
      * more terms must be provided. If only one Term t is provided, the return
      * value will be exactly t.
      */
    @varargs
    def mkAnd(args: Term*): Term = {
        Errors.precondition(args.length > 0, "One or more arguments must be given")
        if(args.length == 1) {
            args(0);
        } else {
            AndList(args.toList)
        }
    }
    
    /** Returns a term representing the conjunction of the given terms. One or
      * more terms must be provided. If only one term t is provided, the return
      * value will be exactly t.
      */
    def mkAnd(args: java.util.List[Term]): Term = {
        Errors.precondition(args.size > 0, "One or more arguments must be given")
        if(args.size == 1) {
            args.get(0);
        } else {
            AndList(args.asScala.toList)
        }
    }
    
    /** Returns a term representing the disjunction of the given terms. One or
      * more terms must be provided. If only one term t is provided, the return
      * value will be exactly t.
      */
    @varargs
    def mkOr(args: Term*): Term = {
        Errors.precondition(args.length > 0, "One or more arguments must be given")
        if(args.length == 1) {
            args(0);
        } else {
            OrList(args.toList)
        }
    }
    
    /** Returns a term representing the conjunction of the given terms. One or
      * more terms must be provided. If only one term t is provided, the return
      * value will be exactly t.
      */
    def mkOr(args: java.util.List[Term]): Term = {
        Errors.precondition(args.size > 0, "One or more arguments must be given")
        if(args.size == 1) {
            args.get(0);
        } else {
            OrList(args.asScala.toList)
        }
    }
    
    /** Returns a Term representing the negation of the given term. */
    def mkNot(body: Term): Term = Not(body)
    
    /** Returns a term representing the implication "t1 implies t2". */
    def mkImp(t1: Term, t2: Term): Term = Implication(t1, t2)
    
    /** Returns a term representing the truth value of whether t1 and t2 are equal.
      * Users should also use this for the bi-equivalence "t1 iff t2".
      */
    def mkEq(t1: Term, t2: Term): Term = Eq(t1, t2)
    
    /** Returns a term representing the constraint that the given terms have
      * distinct values. Two or more terms must be provided
      */
    def mkDistinct(arguments: java.util.List[_ <: Term]): Term = {
        Errors.precondition(arguments.size >= 2, "Two or more arguments must be given")
        Distinct(arguments.asScala.toList)
    }
    
    /** Returns a term representing the constraint that the given terms have
      * distinct values. Two or more terms must be provided.
      */
    @varargs
    def mkDistinct(arguments: Term*): Term = {
        Errors.precondition(arguments.length >= 2, "Two or more arguments must be given")
        Distinct(arguments.toList);
    }
    
    /** Returns a term representing the result of the application of a function with
      * the given functionName to the given arguments. At least one or more arguments
      * must be provided.
      */
    @varargs
    def mkApp(functionName: String, arguments: Term*): Term =
        App(functionName, arguments.toList)
    
    /** Returns a term representing the result of the application of a function with
      * the given functionName to the given arguments. At least one or more arguments
      * must be provided.
      */
    def mkApp(functionName: String, arguments: java.util.List[_ <: Term]): Term =
        App(functionName, arguments.asScala.toList)
    
    /** Returns a term representing the universal quantification of the given body
      * over the given annotated variables.
      * At least one or more variables must be provided.
      */
    def mkForall(vars: java.util.List[AnnotatedVar], body: Term): Term = 
        Forall(vars.asScala.toList, body)
    
    /** Returns a term representing the universal quantification of the given body
      * over the given annotated variable.
      */
    def mkForall(x: AnnotatedVar, body: Term): Term = 
        Forall(List(x), body)
    
    /** Returns a term representing the existential quantification of the given body
      * over the given annotated variables.
      * At least one or more variables must be provided.
      */
    def mkExists(vars: java.util.List[AnnotatedVar], body: Term): Term = 
        Exists(vars.asScala.toList, body)
    
    /** Returns a term representing the existential quantification of the given body
    * over the given annotated variable.
    */
    def mkExists(x: AnnotatedVar, body: Term): Term = 
        Exists(List(x), body)
    
    /** Returns a term representing the bi-equivalence "t1 iff t2". */
    def mkIff(t1: Term, t2: Term): Term = Iff(t1, t2)
    
    def mkTC(functionName: String, arg1: Term, arg2: Term): Term = TC(functionName, arg1, arg2)
    
    /** Internal method for creating Domain Elements. */
    def mkDomainElement(index: Int, sort: Type) = DomainElement(index, sort)
}
