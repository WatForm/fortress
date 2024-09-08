package fortress.operations

import fortress.data.IntSuffixNameGenerator
import fortress.msfol._

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

        def freshVars(vars: Seq[AnnotatedVar], nameMap: Map[String, String]): (Seq[AnnotatedVar], Map[String, String]) = {
            var newNameMap = nameMap
            val newVars = vars map { case AnnotatedVar(Var(name), sort) =>
                val newName = nameGenerator.freshName(name)
                newNameMap = newNameMap + (name -> newName) // overwrite in the sub-context for shadowing
                AnnotatedVar(Var(newName), sort)
            }
            (newVars, newNameMap)
        }

        class RenameTerm(nameMap: Map[String, String]) extends NaturalTermRecursion {
            private def mapName(name: String) = nameMap.getOrElse(name, name)

            override val exceptionalMappings: PartialFunction[Term, Term] = {
                case Var(name) => Var(mapName(name))
                case EnumValue(name) => EnumValue(mapName(name))

                case Forall(vars, body) =>
                    val (newVars, newNameMap) = freshVars(vars, nameMap)
                    Forall(newVars, new RenameTerm(newNameMap).naturalRecur(body))
                case Exists(vars, body) =>
                    val (newVars, newNameMap) = freshVars(vars, nameMap)
                    Exists(newVars, new RenameTerm(newNameMap).naturalRecur(body))
            }
        }
        def renameTerm(term: Term) = new RenameTerm(Map()).naturalRecur(term)

        var newSig = theory.signature
        // these must be done one at a time to avoid our aggressive checking for dependence
        for (cDef <- theory.signature.constantDefinitions) {
            newSig = newSig withoutConstantDefinition cDef
            newSig = newSig withConstantDefinition (cDef mapBody renameTerm)
        }
        for (fDef <- theory.signature.functionDefinitions) {
            // Also rename the arguments to avoid getting out of sync with the body
            newSig = newSig withoutFunctionDefinition fDef
            val (newArgs, newNameMap) = freshVars(fDef.argSortedVar, Map())
            newSig = newSig withFunctionDefinition FunctionDefinition(
                fDef.name, newArgs, fDef.resultSort, new RenameTerm(newNameMap).naturalRecur(fDef.body))
        }

        val newAxioms = theory.axioms map renameTerm
        Theory(newSig, newAxioms)
    }
}
