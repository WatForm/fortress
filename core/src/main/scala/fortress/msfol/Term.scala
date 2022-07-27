package fortress.msfol

import fortress.util.Errors
import fortress.operations._
import fortress.data._
import scala.jdk.CollectionConverters._
import scala.annotation.varargs // So we can call Scala varargs methods from Java

import fortress.operations.TermOps._

/** A syntactic Term in the logic. */
sealed trait Term {
    def accept[T](visitor: TermVisitor[T]): T
    
    def freeVarConstSymbolsJava: java.util.Set[Var] = this.freeVarConstSymbols.asJava
}

/** A term which is a value (for example, True/False, or a value of a sort). */
sealed trait Value extends Term

/** A leaf term in a syntax tree. */
sealed trait LeafTerm extends Term

/** Term that represents True. */
case object Top extends Term with LeafTerm with Value {
    override def toString: String = "true"
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitTop()
}

/** Term that represents Bottom. */
case object Bottom extends Term with LeafTerm with Value {
    override def toString: String = "false"
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitBottom()
}

/** Term that represents a variable (including prime propositions).
  * Variables and constants are treated as syntactically indistinguishable.
  * Whether it is treated as a variable or constant depends on the context
  * in which it is used (e.g. a signature or quantifier binding).
  */
case class Var private(name: String) extends Term with LeafTerm {
    Errors.Internal.precondition(name.length > 0, "Cannot create variable with empty name")
    
    override def toString: String = name
    def getName: String = name
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitVar(this)
    
    /** Returns an AnnotatedVar that represents this variable annotated with
      * with a sort. */
    def of(sort: Sort) = AnnotatedVar(this, sort)
}

object Var
extends ConcreteFactory[Var, String]((name: String) => new Var(name))
with Caching[Var, String] {

    def apply(name: String): Var = {
        Errors.Internal.precondition(! Names.isIllegal(name), "Illegal variable name " + name)
        create(name)
    }
    
    private [msfol] def mkWithoutNameRestriction(name: String): Var = new Var(name)
}

case class EnumValue private (name: String) extends Term with LeafTerm with Value {
    Errors.Internal.precondition(name.length > 0)
    
    override def toString: String = name
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitEnumValue(this)
}

object EnumValue
extends ConcreteFactory[EnumValue, String]((name: String) => new EnumValue(name))
with Caching[EnumValue, String] {

    def apply(name: String): EnumValue = {
        Errors.Internal.precondition(! Names.isIllegal(name))
        create(name)
    }

    private [msfol] def mkWithoutNameRestriction(name: String): EnumValue = new EnumValue(name)
}

/** Represents a negation. */
case class Not private (body: Term) extends Term {
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitNot(this)
    def mapBody(mapping: Term => Term): Term = Not(mapping(body))
    
    override def toString: String = "~(" + body.toString + ")"
}

/** Represents a conjunction. */
case class AndList private (arguments: Seq[Term]) extends Term {
    Errors.Internal.precondition(arguments.size >= 2)
    
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
    
    def smart(args: Seq[Term]): Term = {
        if (args.size == 0) Top
        else if (args.size == 1) args.head
        else AndList(args)
    }
}

/** Represents a disjunction. */
case class OrList private (arguments: Seq[Term]) extends Term {
    Errors.Internal.precondition(arguments.size >= 2)
    
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitOrList(this)
    def mapArguments(mapping: Term => Term): Term =
        OrList(arguments.map(mapping))
    
    override def toString: String = "Or(" + arguments.mkString(", ") + ")"
}

object OrList {
    def apply(args: Term*): Term = OrList(args.toList)
}

object Or {
    def apply(args: Term*): Term = OrList(args.toList)
    
    def smart(args: Seq[Term]): Term = {
        if (args.size == 0) Bottom
        else if (args.size == 1) args.head
        else OrList(args)
    }
}

/** Represents a formula signifying whether its arguments have distinct values. */
case class Distinct private (arguments: Seq[Term]) extends Term {
    Errors.Internal.precondition(arguments.size >= 2)
    
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
        Errors.Internal.assertion(pairs.size() == (n*(n - 1) / 2), "" + n + " terms, but somehow generated " + pairs.size() + " pairs")
        Term.mkAnd(pairs)
    }
    
    override def toString: String = "Distinct(" + arguments.mkString(", ") + ")"
}

object Distinct {
    def apply(arguments: Term*): Term = Distinct(arguments.toList)
}

/** Represents an implication. */
case class Implication private (left: Term, right: Term) extends Term {
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitImplication(this)
    def mapArguments(mapping: Term => Term): Term =
        Implication(mapping(left), mapping(right))
    
    override def toString: String = left.toString + " => " + right.toString
}

/** Represents a bi-equivalence. */
case class Iff private (left: Term, right: Term) extends Term {
    def getLeft: Term = left
    def getRight: Term = right
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitIff(this)
    def mapArguments(mapping: Term => Term): Term =
        Iff(mapping(left), mapping(right))
    
    override def toString: String = left.toString + " <=> " + right.toString
}

/** Represents an equality. */
case class Eq private (left: Term, right: Term) extends Term {
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitEq(this)
    def mapArguments(mapping: Term => Term): Term =
        Eq(mapping(left), mapping(right))
        
    override def toString: String = left.toString + " = " + right.toString
}

/** Represents a function or predicate application. */
case class App private (functionName: String, arguments: Seq[Term]) extends Term {
    Errors.Internal.precondition(functionName.length >= 1, "Empty function name")
    Errors.Internal.precondition(arguments.size >= 1, "Nullary function application " + functionName + " should be a Var")
    
    def getArguments: java.util.List[Term] = arguments.asJava
    def getFunctionName: String = functionName
    override def accept[T](visitor: TermVisitor[T]): T  = visitor.visitApp(this)
    def mapArguments(mapping: Term => Term): Term =
        App(functionName, arguments.map(mapping))
    
    override def toString: String = functionName + "(" + arguments.mkString(", ") + ")"
}


object App
extends ConcreteFactory[App, (String, Seq[Term])] ( (t: (String, Seq[Term])) => new App(t._1, t._2) )
with Caching[App, (String, Seq[Term])] {
    def apply(functionName: String, arguments: Seq[Term]): App = create((functionName, arguments))
    def apply(functionName: String, args: Term*): Term = App(functionName, args.toList)
}

case class BuiltinApp private (function: BuiltinFunction, arguments: Seq[Term]) extends Term {
    Errors.Internal.precondition(arguments.size >= 1, "Nullary builtin function application " + function)
    
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitBuiltinApp(this)
    
    def mapArguments(mapping: Term => Term): Term =
        BuiltinApp(function, arguments.map(mapping))
}

object BuiltinApp {
    def apply(function: BuiltinFunction, args: Term*): Term = BuiltinApp(function, args.toList)
}

sealed trait Quantifier extends Term {
    def vars: Seq[AnnotatedVar]
    def body: Term
    def mapBody(mapping: Term => Term): Term
}

/** Represents an existentially quantified Term. */
case class Exists private (vars: Seq[AnnotatedVar], body: Term) extends Quantifier {
    Errors.Internal.precondition(vars.size >= 1, "Quantifier must bind at least one variable");
    // Check variables distinct
    Errors.Internal.precondition(vars.map(av => av.name).toSet.size == vars.size, "Duplicate variable name in quantifier")
    
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitExists(this)
    def mapBody(mapping: Term => Term): Term = Exists(vars, mapping(body))
    
    override def toString: String = "exists " + vars.mkString(", ") + " . " + body.toString
    
    def varsJava: java.util.List[AnnotatedVar] = vars.asJava
}

object Exists {
    def apply(variable: AnnotatedVar, body: Term): Exists = Exists(Seq(variable), body)
}

/** Represents a universally quantified Term. */
case class Forall private (vars: Seq[AnnotatedVar], body: Term) extends Quantifier {
    Errors.Internal.precondition(vars.size >= 1, "Quantifier must bind at least one variable")
    // Check variables distinct
    Errors.Internal.precondition(vars.map(av => av.name).toSet.size == vars.size, "Duplicate variable name in quantifier")
    
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitForall(this)
    def mapBody(mapping: Term => Term): Term = Forall(vars, mapping(body))
    
    override def toString: String = "forall " + vars.mkString(", ") + " . " + body.toString
    
    def varsJava: java.util.List[AnnotatedVar] = vars.asJava
}

object Forall {
    def apply(variable: AnnotatedVar, body: Term): Forall = Forall(Seq(variable), body)
}

/** Represents an indexed domain element.
  * For example, DomainElement(2, A) represents the domain element at index 2
  * for sort A, written as 2A.
  * DomainElements are indexed starting with 1.*/
case class DomainElement private (index: Int, sort: Sort) extends Term with LeafTerm with Value {
    Errors.Internal.precondition(index >= 1)
    
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitDomainElement(this)
    
    // TODO need to restrict any other code from using this naming convention
    val asSmtConstant: Var = Var.mkWithoutNameRestriction(DomainElement.prefix + index.toString + sort.toString)

    val asEnumValue: EnumValue = EnumValue.mkWithoutNameRestriction(DomainElement.prefix + index.toString + sort.toString)

    override def toString = DomainElement.prefix + index.toString + sort.toString
}

object DomainElement
extends ConcreteFactory[DomainElement, (Int, Sort)]( (t: (Int, Sort)) => new DomainElement(t._1, t._2) )
with Caching[DomainElement, (Int, Sort)] {
    def apply(index: Int, sort: Sort): DomainElement = create((index, sort))

    private[msfol] val prefix = "_@"
    
    def interpretName(name: String): Option[DomainElement] = {
        if(name startsWith DomainElement.prefix) {
            val s = name drop DomainElement.prefix.length
            val ints = Set('0', '1', '2', '3', '4', '5', '6', '7', '8', '9')
            val i = s.indexWhere(!ints.contains(_))
            val (indexStr, sortStr) = s splitAt i
            Some(DomainElement(indexStr.toInt, SortConst(sortStr)))
        } else None
    }
    
    def range(rangeOver: Range, sort: Sort): IndexedSeq[DomainElement] =
        rangeOver map (i => DomainElement(i, sort))
    
    implicit val ordering: math.Ordering[DomainElement] = math.Ordering.fromLessThan(_.index < _.index)
}

case class IntegerLiteral private (value: Int) extends Term with LeafTerm with Value {
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitIntegerLiteral(this)
}

case class BitVectorLiteral private (value: Int, bitwidth: Int) extends Term with LeafTerm with Value {
    Errors.Internal.precondition(bitwidth > 0)
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitBitVectorLiteral(this)
}

case class IfThenElse private (condition: Term, ifTrue: Term, ifFalse: Term) extends Term {
    override def accept[T](visitor: TermVisitor[T]): T = visitor.visitIfThenElse(this)
}

/** Represents a transitive closure application. */
case class Closure private (functionName: String, arg1: Term, arg2: Term) extends Term {
    Errors.Internal.precondition(functionName.length >= 1, "Empty function name in transitive closure")
    // Errors.Internal.precondition(arguments.size >= 2, "Function application ^" + functionName + " should have at least 2 arguments")

    def arguments: Seq[Term] = Seq(arg1, arg2)
    def getArguments: java.util.List[Term] = Seq(arg1, arg2).asJava
    def getFunctionName: String = functionName
    override def accept[T](visitor: TermVisitor[T]): T  = visitor.visitClosure(this)
    def mapArguments(mapping: Term => Term): Term =
        Closure(functionName, mapping(arg1), mapping(arg2))

    override def toString: String = "^" + functionName + "(" + arg1.toString() + ", " + arg2.toString() + ")"
}

/** Represents a reflexive transitive closure application. */
case class ReflexiveClosure private (functionName: String, arg1: Term, arg2: Term) extends Term {
    Errors.Internal.precondition(functionName.length >= 1, "Empty function name in reflexive transitive closure")
    // Errors.Internal.precondition(arguments.size >= 2, "Function application *" + functionName + " should have at least 2 arguments")
    def arguments: Seq[Term] = Seq(arg1, arg2)
    def getArguments: java.util.List[Term] = Seq(arg1, arg2).asJava
    def getFunctionName: String = functionName
    override def accept[T](visitor: TermVisitor[T]): T  = visitor.visitReflexiveClosure(this)
    def mapArguments(mapping: Term => Term): Term =
        ReflexiveClosure(functionName, mapping(arg1), mapping(arg2))

    override def toString: String = "*" + functionName + "(" + arg1.toString() + ", " + arg2.toString() + ")"
}

/** Companion object for Term. */
object Term {
    /** Returns a Term representing Top/Verum */
    val mkTop = Top
    
    /** Returns a Term representing Bottom/Falsum */
    val mkBottom = Bottom
    
    /** Returns a Term representing the variable (or constant, depending on the
      * context in which it is used) with the given name.
      */
    def mkVar(name: String): Var = Var(name)
    
    def mkEnumValue(name: String): EnumValue = EnumValue(name)
    
    /** Returns a Term representing the conjunction of the given terms. One or
      * more terms must be provided. If only one Term t is provided, the return
      * value will be exactly t.
      */
    @varargs
    def mkAnd(args: Term*): Term = {
        Errors.Internal.precondition(args.length > 0, "One or more arguments must be given")
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
        Errors.Internal.precondition(args.size > 0, "One or more arguments must be given")
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
        Errors.Internal.precondition(args.length > 0, "One or more arguments must be given")
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
        Errors.Internal.precondition(args.size > 0, "One or more arguments must be given")
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
        Errors.Internal.precondition(arguments.size >= 2, "Two or more arguments must be given")
        Distinct(arguments.asScala.toList)
    }
    
    /** Returns a term representing the constraint that the given terms have
      * distinct values. Two or more terms must be provided.
      */
    @varargs
    def mkDistinct(arguments: Term*): Term = {
        Errors.Internal.precondition(arguments.length >= 2, "Two or more arguments must be given")
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
    
    /** Returns a term representing the bi-implication "t1 iff t2". */
    def mkIff(t1: Term, t2: Term): Term = Iff(t1, t2)
    
    def mkIfThenElse(condition: Term, ifTrue: Term, ifFalse: Term): Term = IfThenElse(condition, ifTrue, ifFalse)

    def mkClosure(functionName: String, arg1: Term, arg2: Term): Term =
        Closure(functionName, arg1, arg2)
    def mkClosure(app: App, arg1: Term, arg2: Term): Term =
        Closure(app.functionName, arg1, arg2)

    def mkReflexiveClosure(functionName: String, arg1: Term, arg2: Term): Term =
        ReflexiveClosure(functionName, arg1, arg2)
    def mkReflexiveClosure(app: App, arg1: Term, arg2: Term): Term =
        ReflexiveClosure(app.functionName, arg1, arg2)

    def mkPlus(t1: Term, t2: Term): Term = BuiltinApp(IntPlus, Seq(t1, t2))
    def mkNeg(t: Term): Term = BuiltinApp(IntNeg, Seq(t))
    def mkSub(t1: Term, t2: Term): Term = BuiltinApp(IntSub, Seq(t1, t2))
    def mkMult(t1: Term, t2: Term): Term = BuiltinApp(IntMult, Seq(t1, t2))
    def mkDiv(t1: Term, t2: Term): Term = BuiltinApp(IntDiv, Seq(t1, t2))
    def mkMod(t1: Term, t2: Term): Term = BuiltinApp(IntMod, Seq(t1, t2))
    def mkLE(t1: Term, t2: Term): Term = BuiltinApp(IntLE, Seq(t1, t2))
    def mkLT(t1: Term, t2: Term): Term = BuiltinApp(IntLT, Seq(t1, t2))
    def mkGE(t1: Term, t2: Term): Term = BuiltinApp(IntGE, Seq(t1, t2))
    def mkGT(t1: Term, t2: Term): Term = BuiltinApp(IntGT, Seq(t1, t2))

    def mkBvPlus(t1: Term, t2: Term): Term = BuiltinApp(BvPlus, Seq(t1, t2))
    def mkBvNeg(t: Term): Term = BuiltinApp(BvNeg, Seq(t))
    def mkBvSub(t1: Term, t2: Term): Term = BuiltinApp(BvSub, Seq(t1, t2))
    def mkBvMult(t1: Term, t2: Term): Term = BuiltinApp(BvMult, Seq(t1, t2))
    def mkBvSignedDiv(t1: Term, t2: Term): Term = BuiltinApp(BvSignedDiv, Seq(t1, t2))
    def mkBvSignedMod(t1: Term, t2: Term): Term = BuiltinApp(BvSignedMod, Seq(t1, t2))
    def mkBvSignedLE(t1: Term, t2: Term): Term = BuiltinApp(BvSignedLE, Seq(t1, t2))
    def mkBvSignedLT(t1: Term, t2: Term): Term = BuiltinApp(BvSignedLT, Seq(t1, t2))
    def mkBvSignedGE(t1: Term, t2: Term): Term = BuiltinApp(BvSignedGE, Seq(t1, t2))
    def mkBvSignedGT(t1: Term, t2: Term): Term = BuiltinApp(BvSignedGT, Seq(t1, t2))

    /** Internal method for creating Domain Elements. */
    def mkDomainElement(index: Int, sort: Sort) = DomainElement(index, sort)
}
