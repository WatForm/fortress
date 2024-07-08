package fortress.operations

import fortress.data.IntSuffixNameGenerator
import fortress.msfol._

import scala.collection.mutable

/**
  * Alpha-rename all quantified variables in a theory such that they do not conflict with each other
  * (even in unrelated parts of the theory) or any elements of the signature.
  * Does not modify the signature (other than the bodies of definitions) or any function names.
  */
object MaxAlphaRenaming {
    def rename(theory: Theory): Theory = {
        val nameGenerator = new IntSuffixNameGenerator(Set(), 0)
        for (sort <- theory.signature.sorts) nameGenerator.forbidName(sort.name)
        for (funcDecl <- theory.signature.functionDeclarations) nameGenerator.forbidName(funcDecl.name)
        for (funcDefn <- theory.signature.functionDefinitions) nameGenerator.forbidName(funcDefn.name)
        for (constDecl <- theory.signature.constantDeclarations) nameGenerator.forbidName(constDecl.name)
        for (constDefn <- theory.signature.constantDefinitions) nameGenerator.forbidName(constDefn.name)
        for (enumConstList <- theory.signature.enumConstants.values)
            for (enumConst <- enumConstList)
                nameGenerator.forbidName(enumConst.name)

        val nameMap = mutable.Map[String, String]()

        def mapName(name: String) = nameMap.getOrElse(name, name)
        def freshName(name: String) = {
            val newName = nameGenerator.freshName(name)
            nameMap(name) = newName
            newName
        }

        def freshVars(vars: Seq[AnnotatedVar]) = vars map {
            case AnnotatedVar(Var(name), sort) => AnnotatedVar(Var(freshName(name)), sort)
        }

        object RenameTerm extends NaturalTermRecursion {
            override val exceptionalMappings: PartialFunction[Term, Term] = {
                case Var(name) => Var(mapName(name))
                case EnumValue(name) => EnumValue(mapName(name))

                case Forall(vars, body) => Forall(freshVars(vars), naturalRecur(body))
                case Exists(vars, body) => Exists(freshVars(vars), naturalRecur(body))
            }
        }
        def renameTerm(term: Term) = RenameTerm.naturalRecur(term)

        var newSig = theory.signature
        // these must be done one at a time to avoid our aggressive checking for dependence
        for (cDef <- theory.signature.constantDefinitions) {
            newSig = newSig withoutConstantDefinition cDef
            newSig = newSig withConstantDefinition (cDef mapBody renameTerm)
        }
        for (fDef <- theory.signature.functionDefinitions) {
            newSig = newSig withoutFunctionDefinition fDef
            newSig = newSig withFunctionDefinition (fDef mapBody renameTerm)
        }

        val newAxioms = theory.axioms map renameTerm
        Theory(newSig, newAxioms)
    }
}
