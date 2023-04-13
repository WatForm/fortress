package fortress.operations

import fortress.msfol._

import scala.collection.mutable
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
        case Closure(_, arg1, arg2, args) => (args :+ arg1 :+ arg2) map depthQuantification reduce max
        case ReflexiveClosure(_, arg1, arg2, args) => (args :+ arg1 :+ arg2) map depthQuantification reduce max
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
        case Closure(_, arg1, arg2, args) => ((args :+ arg1 :+ arg2) map depthQuantification reduce max) + 1
        case ReflexiveClosure(_, arg1, arg2, args) => ((args :+ arg1 :+ arg2) map depthQuantification reduce max) + 1
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
        case Closure(_, arg1, arg2, args) => termCount(arg1) + termCount(arg2) + (args map termCount reduce (_ + _)) + 1
        case ReflexiveClosure(_, arg1, arg2, args) => termCount(arg1) + termCount(arg2) + (args map termCount reduce (_ + _)) + 1
        case Top | Bottom | Var(_) | EnumValue(_) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => 1
        case IfThenElse(condition, ifTrue, ifFalse) => (List(condition, ifTrue, ifFalse) map termCount).sum + 1
    }

    // Returns the number of nodes in a term
    def declarationCountMap(term: Term, profilingInfo: mutable.Map[Declaration, Int]): Unit = term match {
        case Forall(_, body) => declarationCountMap(body, profilingInfo)
        case Exists(_, body) => declarationCountMap(body, profilingInfo)
        case AndList(args) => args.foreach(arg => declarationCountMap(arg, profilingInfo))
        case OrList(args) => args.foreach(arg => declarationCountMap(arg, profilingInfo))
        case Not(body) => declarationCountMap(body, profilingInfo)
        case Distinct(args) => args.foreach(arg => declarationCountMap(arg, profilingInfo))
        case Implication(p, q) =>
            declarationCountMap(p, profilingInfo)
            declarationCountMap(q, profilingInfo)
        case Iff(p, q) =>
            declarationCountMap(p, profilingInfo)
            declarationCountMap(q, profilingInfo)
        case Eq(p, q) =>
            declarationCountMap(p, profilingInfo)
            declarationCountMap(q, profilingInfo)
        case App(funcName, args) =>
            if(profilingInfo.keySet.filter(pred => pred.isInstanceOf[FuncDecl] && pred.asInstanceOf[FuncDecl].name.equals(funcName)).isEmpty)
                println("funcName: " + funcName)
            val funcDecl = profilingInfo.keySet.filter(pred => pred.isInstanceOf[FuncDecl] && pred.asInstanceOf[FuncDecl].name.equals(funcName)).head
            profilingInfo(funcDecl) = profilingInfo(funcDecl) + 1
            args.foreach(arg => declarationCountMap(arg, profilingInfo))
        case BuiltinApp(_, args) => args.foreach(arg => declarationCountMap(arg, profilingInfo))
        case Closure(_, arg1, arg2, args) => (Seq(arg1, arg2) ++ args).foreach(arg => declarationCountMap(arg, profilingInfo))
        case ReflexiveClosure(_, arg1, arg2, args) => (Seq(arg1, arg2) ++ args).foreach(arg => declarationCountMap(arg, profilingInfo))
        case Var(name) =>
            val annotatedVar = profilingInfo.keySet.filter(pred => pred.isInstanceOf[AnnotatedVar] && pred.asInstanceOf[AnnotatedVar].name.equals(name))
            // if it is a constant and can be found in the map keys
            if (annotatedVar.size == 1) {
                val annotatedVarDecl = annotatedVar.head
                profilingInfo(annotatedVarDecl) = profilingInfo(annotatedVarDecl) + 1
            }
        case Top | Bottom | EnumValue(_) | DomainElement(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => ()
        case IfThenElse(condition, ifTrue, ifFalse) => List(condition, ifTrue, ifFalse).foreach(arg => declarationCountMap(arg, profilingInfo))
    }
}
