package fortress.operations

import fortress.msfol._
import scala.math.max

object TermMetrics {
  // Returns depth of quantification of a term
  def depthQuantification(term: Term): Int = term match {
    case Forall(vars, body) => depthQuantification(body) + vars.length
    case Exists(vars, body) => depthQuantification(body) + vars.length
    case AndList(args) => args.map(depthQuantification).max
    case OrList(args) => args.map(depthQuantification).max
    case Not(body) => depthQuantification(body)
    case Distinct(args) => args.map(depthQuantification).max
    case Implication(p, q) => max(depthQuantification(p), depthQuantification(q))
    case Iff(p, q) => max(depthQuantification(p), depthQuantification(q))
    case Eq(p, q) => max(depthQuantification(p), depthQuantification(q))
    case App(_, args) => args.map(depthQuantification).max
    case BuiltinApp(_, args) => args.map(depthQuantification).max
    case Closure(_, args, _, _) => args.map(depthQuantification).max
    case ReflexiveClosure(_, args, _, _) => args.map(depthQuantification).max
    case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => 0
    case IfThenElse(condition, ifTrue, ifFalse) => (List(condition, ifTrue, ifFalse) map depthQuantification).max
  }

  // Returns depth of nested functions of a term
  def depthNestedFunc(term: Term): Int = term match {
    case Forall(_, body) => depthNestedFunc(body)
    case Exists(_, body) => depthNestedFunc(body)
    case AndList(args) => args.map(depthNestedFunc).max
    case OrList(args) => args.map(depthNestedFunc).max
    case Not(body) => depthNestedFunc(body)
    case Distinct(args) => args.map(depthNestedFunc).max
    case Implication(p, q) => max(depthNestedFunc(p), depthNestedFunc(q))
    case Iff(p, q) => max(depthNestedFunc(p), depthNestedFunc(q))
    case Eq(p, q) => max(depthNestedFunc(p), depthNestedFunc(q))
    case App(_, args) => args.map(depthNestedFunc).max + 1
    case BuiltinApp(_, args) => args.map(depthNestedFunc).max + 1
    case Closure(_, args, _, _) => args.map(depthNestedFunc).max + 1
    case ReflexiveClosure(_, args, _, _) => args.map(depthNestedFunc).max + 1
    case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => 0
    case IfThenElse(condition, ifTrue, ifFalse) => (List(condition, ifTrue, ifFalse) map depthNestedFunc).max
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
    case BuiltinApp(_, args) => args.map(termCount).sum + 1
    case Closure(_, args, _, _) => args.map(termCount).sum + 1
    case ReflexiveClosure(_, args, _, _) => args.map(termCount).sum + 1
    case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => 1
    case IfThenElse(condition, ifTrue, ifFalse) => (List(condition, ifTrue, ifFalse) map termCount).sum + 1
  }
}
