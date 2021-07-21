package fortress.operations

import scala.language.implicitConversions
import fortress.msfol._

import scala.collection.mutable


case class IllegalNameSubstitution(affix: String) {
    def newName(name: String): String = affix + name + affix

    // Replace all illegal names in a Term, and updating the map.
    def apply(term: Term, renameMap: mutable.Map[String, String]): Term = term match {
        case Var(name) =>
            // If it has been renamed before, we rename it to the same new name as before
            if (renameMap.contains(name)) Var(renameMap(name))
            // if it collides with some new names we introduced, we rename it to something else
            else if (renameMap.valuesIterator.exists(_.equals(name)) || Names.isIllegal(name)) {
                renameMap += name -> newName(name)
                Var(renameMap(name))
            } else term
        case Top | Bottom => term
        case Not(p) => Not(apply(p, renameMap))
        case AndList(args) => AndList(args map (arg => apply(arg, renameMap)))
        case OrList(args) => OrList(args map (arg => apply(arg, renameMap)))
        case Distinct(args) => Distinct(args map (arg => apply(arg, renameMap)))
        case Implication(p, q) => Implication(apply(p, renameMap), apply(q, renameMap))
        case Iff(p, q) => Iff(apply(p, renameMap), apply(q, renameMap))
        case Eq(l, r) => Eq(apply(l, renameMap), apply(r, renameMap))
        case App(name, args) => App(renameMap.getOrElse(name, name), args map (arg => apply(arg, renameMap)))
        case Closure(name, args, arg1, arg2) => Closure(renameMap.getOrElse(name, name), args map (arg => apply(arg, renameMap)), apply(arg1, renameMap), apply(arg2, renameMap))
        case ReflexiveClosure(name, args, arg1, arg2) => ReflexiveClosure(renameMap.getOrElse(name, name), args map (arg => apply(arg, renameMap)), apply(arg1, renameMap), apply(arg2, renameMap))
        case Exists(avars, body) =>
            val newVars = avars map { avar => Var(renameMap.getOrElse(avar.name, avar.name)) of avar.sort }
            Exists(newVars, apply(body, renameMap))
        case Forall(avars, body) =>
            val newVars = avars map { avar => Var(renameMap.getOrElse(avar.name, avar.name)) of avar.sort }
            Forall(newVars, apply(body, renameMap))
        case DomainElement(index, sort) => term
        case EnumValue(_) | BuiltinApp(_, _) | IntegerLiteral(_) | BitVectorLiteral(_, _) => term
        case IfThenElse(condition, ifTrue, ifFalse) => IfThenElse(apply(condition, renameMap), apply(ifTrue, renameMap), apply(ifFalse, renameMap))
    }

    // Replace all illegal names in a Signature, and updating the map.
    def apply(signature: Signature, renameMap: mutable.Map[String, String]): Signature = signature match {
        case Signature(sorts, functionDeclarations, constants, enumConstants) => {
            val newConstants = constants map { constant =>
                if (renameMap.contains(constant.name)) {
                    // If it has been renamed already, we simply rename it as before
                    AnnotatedVar(Var(renameMap(constant.name)), constant.sort)
                } else if (renameMap.valuesIterator.exists(_.equals(constant.name)) || Names.isIllegal(constant.name)) {
                    // If it is an illegal name, we rename it and added to the map
                    renameMap += constant.name -> newName(constant.name)
                    AnnotatedVar(Var(renameMap(constant.name)), constant.sort)
                } else constant
            }
            val newFunctions = functionDeclarations map { funcDecl =>
                if (renameMap.contains(funcDecl.name)) {
                    // If it has been renamed already, we simply rename it as before
                    FuncDecl(renameMap(funcDecl.name), funcDecl.argSorts, funcDecl.resultSort)
                } else if (renameMap.valuesIterator.exists(_.equals(funcDecl.name)) || Names.isIllegal(funcDecl.name)) {
                    // If it is an illegal name, we rename it and added to the map
                    renameMap += funcDecl.name -> newName(funcDecl.name)
                    FuncDecl(renameMap(funcDecl.name), funcDecl.argSorts, funcDecl.resultSort)
                } else funcDecl
            }

            Signature(
                sorts,
                newFunctions,
                newConstants,
                enumConstants
            )
        }
    }

    // Replace all illegal names in a Theory, and updating the map.
    def apply(theory: Theory, renameMap: mutable.Map[String, String]): Theory = {
        Theory.mkTheoryWithSignature(apply(theory.signature, renameMap))
          .withAxioms(theory.axioms map (axiom => apply(axiom, renameMap)))
    }
}
