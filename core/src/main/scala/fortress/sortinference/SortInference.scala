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
        val freshSortsConstantsMap: Map[String, Sort] = theory.constantDeclarations.map {c => c.name -> freshSubstitution(c).sort}.toMap
        
        // Associate each function with a collection of fresh sorts
        // Functions with declarations
        val freshFuncDeclMap: Map[FuncDecl, FuncDecl] = theory.functionDeclarations.map(f => (f -> freshSubstitution(f))).toMap
        val freshFuncDeclMapExpanded: Map[String, (Seq[Sort], Sort)] = theory.functionDeclarations.map { f => {
            val fSub = freshFuncDeclMap(f)
            f.name -> (fSub.argSorts, fSub.resultSort)
        }}.toMap
        // Functions with definitions
        val freshFuncDefnMap: Map[FunctionDefinition, FunctionDefinition] = theory.functionDefinitions.map(f => (f -> freshSubstitution(f))).toMap
        val freshFuncDefnMapExpanded: Map[String, (Seq[Sort], Sort)] = theory.functionDefinitions.map { f => {
            val fSub = freshFuncDefnMap(f)
            f.name -> (fSub.argSorts, fSub.resultSort)
        }}.toMap
        // All functions
        val freshSortsFuncMap = freshFuncDeclMapExpanded.concat(freshFuncDefnMapExpanded)
        
        // Maps original theory axiom to fresh axiom
        val freshAxioms: Map[Term, Term] = { theory.axioms map (ax => ax -> freshSubstitution(ax)) }.toMap
        
        // Gather equations from axioms and function definition bodies
        // val funcDefnAxioms = freshSortsFuncD
        val funcDefnAxioms = freshFuncDefnMap.values.map(_.asAxiom).toSet
        val equations: Set[Equation] = Equation.accumulate(freshSortsConstantsMap, freshSortsFuncMap, freshAxioms.values.toSet union funcDefnAxioms)
        
        // Solve equations, giving substitution from fresh theory to general theory
        val sortSubstitution = Equation.unify(equations.toList)
        
        // Create new signature and terms using substitution
        val newConstants: Set[AnnotatedVar] = theory.constantDeclarations map (av => {
            Var(av.name) of sortSubstitution(freshSortsConstantsMap(av.name))
        })
        val newFunctionDeclarations: Set[FuncDecl] = theory.functionDeclarations map (f => {sortSubstitution(freshFuncDeclMap(f))})
        val newFunctionDefinitions: Set[FunctionDefinition] = theory.functionDefinitions.map (f => {sortSubstitution(freshFuncDefnMap(f))})
        
        // Maps original theory axiom to general axiom 
        val generalAxioms: Map[Term, Term] = for((originAx, freshAx) <- freshAxioms) yield (originAx -> sortSubstitution(freshAx))
        
        val usedSorts: Set[Sort] = (0 to (freshSubstitution.index - 1)).map(freshSubstitution.sortVar(_)).map(sortSubstitution(_)).toSet
        
        val generalTheory = Theory.empty
            .withSorts(usedSorts.toSeq : _*)
            .withConstantDeclarations(newConstants)
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