package fortress.sortinference

import fortress.msfol._
import fortress.util.Errors
import scala.collection.mutable
import fortress.data._
import scala.language.implicitConversions

object SortInference {
    
    // Given a theory, computes the most generally-sorted form of that theory (first return value), and a sort substitution (second return value) that maps the generally-sorted theory to the original input theory
    def inferSorts(theory: Theory): (Theory, SortSubstitution) = {
        // Bool, Int, BitVector don't need to be factored into equation solving.
        // Only solve equations between sort variables.
        
        val freshSubstitution = new FreshCountingSubstitution
        
        // Associate each constant with a fresh sort variable
        // Constants with declarations
        val freshConstDeclMap: Map[AnnotatedVar, AnnotatedVar] = theory.constantDeclarations.map(c => c -> freshSubstitution(c)).toMap
        // Constants with definitions
        val freshConstDefnMap: Map[ConstantDefinition, ConstantDefinition] = theory.constantDefinitions.map(c => c -> freshSubstitution(c)).toMap
        // All constants
        val constantLookupTable: Map[String, AnnotatedVar] = freshConstDeclMap.map{case (originalAv, newAv) => originalAv.name -> newAv} ++ freshConstDefnMap.map{case (originalDefn, newDefn) => originalDefn.name -> newDefn.avar}
        
        // Associate each function with a collection of fresh sorts
        // Functions with declarations
        val freshFuncDeclMap: Map[FuncDecl, FuncDecl] = theory.functionDeclarations.map(f => (f -> freshSubstitution(f))).toMap
        // Functions with definitions
        val freshFuncDefnMap: Map[FunctionDefinition, FunctionDefinition] = theory.functionDefinitions.map(f => (f -> freshSubstitution(f))).toMap
        // All functions
        val functionLookupTable: Map[String, FuncDecl] = freshFuncDeclMap.map{case (originalDecl, newDecl) => originalDecl.name -> newDecl} ++ freshFuncDefnMap.map{case (originalDefn, newDefn) => originalDefn.name -> newDefn.asDeclWithoutBody}
        
        // Maps original theory axiom to fresh axiom
        val freshAxioms: Map[Term, Term] = { theory.axioms map (ax => ax -> freshSubstitution(ax)) }.toMap
        
        // Gather equations from axioms and definition bodies
        val constDefnAxioms = freshConstDefnMap.values.map(_.asAxiom).toSet
        val funcDefnAxioms = freshFuncDefnMap.values.map(_.asAxiom).toSet
        val temporaryAxioms = constDefnAxioms union funcDefnAxioms
        val equations: Set[Equation] = Equation.accumulate(constantLookupTable, functionLookupTable, freshAxioms.values.toSet union temporaryAxioms)
        
        // Solve equations, giving substitution from fresh theory to general theory
        val sortSubstitution = Equation.unify(equations.toList)
        
        // Create new signature and terms using substitution
        val newConstantDeclarations: Set[AnnotatedVar] = theory.constantDeclarations.map(av => sortSubstitution(freshConstDeclMap(av)))
        val newConstantDefintions: Set[ConstantDefinition] = theory.constantDefinitions.map(cdef => sortSubstitution(freshConstDefnMap(cdef)))
        val newFunctionDeclarations: Set[FuncDecl] = theory.functionDeclarations.map(f => sortSubstitution(freshFuncDeclMap(f)))
        val newFunctionDefinitions: Set[FunctionDefinition] = theory.functionDefinitions.map(f => sortSubstitution(freshFuncDefnMap(f)))
        
        // Maps original theory axiom to general axiom 
        val generalAxioms: Map[Term, Term] = for((originAx, freshAx) <- freshAxioms) yield (originAx -> sortSubstitution(freshAx))
        
        val usedSorts: Set[Sort] = (0 to (freshSubstitution.index - 1)).map(freshSubstitution.sortVar(_)).map(sortSubstitution(_)).toSet
        
        val generalTheory = Theory.empty
            .withSorts(usedSorts.toSeq : _*)
            .withConstantDeclarations(newConstantDeclarations)
            .withConstantDefinitions(newConstantDefintions)
            .withFunctionDeclarations(newFunctionDeclarations)
            .withFunctionDefinitions(newFunctionDefinitions)
            .withAxioms(generalAxioms.values)
        
        // Now have to compute substitution to go from general theory to original theory
        val substitutionsFromTerms = for((originalAx, generalAx) <- generalAxioms) yield SortSubstitution.computeTermMapping(generalAx, originalAx)
        val substitutionFromSignature = SortSubstitution.computeSigMapping(generalTheory.signature, theory.signature)
        val substitution = substitutionsFromTerms.foldLeft(substitutionFromSignature)((sub, next) => sub union next)
        
        // If the substitution does nothing except rename sorts (i.e. sort inference did nothing)
        // then just return the original theory
        // Otherwise, return the more general inferred theory
        if(substitution.isBijectiveRenaming)
            (theory, SortSubstitution.identity)
        else (generalTheory, substitution)
    }
    
}