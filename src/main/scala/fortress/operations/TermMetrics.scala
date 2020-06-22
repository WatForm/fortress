package fortress.operations

import fortress.msfol._
import scala.math.max

object TermMetrics {
  // Returns depth of quantification of a term
  def depthQuantification(term: Term): Int = depQuant(term)._1

  /* Returns depth of quantification of a term and an integer between 0 and 2 indicating
  * what the current term is. 1 stands for Forall, 2 stands for Exists, 0 stands for it
  * is not a quantifier
  * Sort of current term is used in counting adjacent nested quantifiers.
  * "Forall x, Forall y,..." will be counted as depth 1.
  */
  def depQuant(term: Term): (Int, Int) = term match {
    case Forall(_, body) =>
      val (depth, previousSort) = depQuant(body)
      if (previousSort == 1)
        (depth, 1)
      else
        (depth + 1, 1)
    case Exists(_, body) =>
      val (depth, previousSort) = depQuant(body)
      if (previousSort == 2)
        (depth, 2)
      else
        (depth + 1, 2)
    case AndList(args) => (args.map(depQuant).map(_._1).max, 0)
    case OrList(args) => (args.map(depQuant).map(_._1).max, 0)
    case Top | Bottom | Var(_) | EnumValue(_) => (0, 0)
    case Not(body) => (depQuant(body)._1, 0)
    case Distinct(args) => (args.map(depQuant).map(_._1).max, 0)
    case Implication(p, q) => (List(depQuant(p)._1, depQuant(q)._1).max, 0)
    case Iff(p, q) => (List(depQuant(p)._1, depQuant(q)._1).max, 0)
    case Eq(p, q) => (List(depQuant(p)._1, depQuant(q)._1).max, 0)
    case App(_, args) => (args.map(depQuant).map(_._1).max, 0)
    case BuiltinApp(_, _) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => (0, 0)
  }

  // Returns depth of nested functions of a term
  def depthNestedFunc(term: Term): Int = term match {
    case Forall(_, body) => depthNestedFunc(body)
    case Exists(_, body) => depthNestedFunc(body)
    case AndList(args) => args.map(depthNestedFunc).max
    case OrList(args) => args.map(depthNestedFunc).max
    case Top | Bottom | Var(_) | EnumValue(_) => 0;
    case Not(body) => depthNestedFunc(body)
    case Distinct(args) => args.map(depthNestedFunc).max
    case Implication(p, q) => max(depthNestedFunc(p), depthNestedFunc(q))
    case Iff(p, q) => max(depthNestedFunc(p), depthNestedFunc(q))
    case Eq(p, q) => max(depthNestedFunc(p), depthNestedFunc(q))
    case App(_, args) => args.map(depthNestedFunc).max + 1
    case BuiltinApp(_, _) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => 0
  }

  // Returns the number of nodes in a term
  def termCount(term: Term): Int = term match {
    case Forall(_, body) => termCount(body) + 1
    case Exists(_, body) => termCount(body) + 1
    case AndList(args) => args.map(termCount).sum + 1
    case OrList(args) => args.map(termCount).sum + 1
    case Not(body) => termCount(body) + 1
    case Distinct(args) => args.map(termCount).sum + 1
    case Implication(p, q) => termCount(p) + termCount(q) + 1
    case Iff(p, q) => termCount(p) + termCount(q) + 1
    case Eq(p, q) => termCount(p) + termCount(q) + 1
    case App(_, args) => args.map(termCount).sum + 1
    case Top | Bottom | Var(_) | EnumValue(_) => 1
    case BuiltinApp(_, _) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => 1
  }
}

