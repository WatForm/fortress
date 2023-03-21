package fortress.sortinference

import fortress.msfol._
import fortress.util.Errors
import scala.collection.mutable
import fortress.data._
import scala.language.implicitConversions

// Only allows for Bool and SortConst
object SortInference {
    
    def inferSorts(theory: Theory): (Theory, SortSubstitution) = {
        /** 
            Booleans don't need to be factored into equation solving.
            Only solve equations between type variables.
        */
        def sortVar(index: Int): SortConst = SortConst("S" + index.toString)
        
        def sortVarAsInt(s: SortConst): Int = s.name.tail.toInt
        
        object freshSubstitution extends GeneralSortSubstitution {
            var index = 0
            def freshInt(): Int = {
                val temp = index
                index += 1
                temp
            }
            
            override def apply(sort: Sort) = sort match {
                case SortConst(_) => sortVar(freshInt())
                case sort => sort
            }
        }
        
        // Associate each constant with a fresh sort variable
        val constantMap: Map[String, Sort] = theory.constantDeclarations.map {c => c.name -> freshSubstitution(c).sort}.toMap
        
        // Associate each function with a collection of fresh sorts
        val fnMap: Map[String, (Seq[Sort], Sort)] = theory.functionDeclarations.map { f => {
            val f_sub = freshSubstitution(f)
            f.name -> (f_sub.argSorts, f_sub.resultSort)
        }}.toMap
        
        // Maps original theory axiom to fresh axiom
        val freshAxioms: Map[Term, Term] = { theory.axioms map (ax => ax -> freshSubstitution(ax)) }.toMap
        
        // Gather equations
        val equations: Set[Equation] = Equation.accumulate(constantMap, fnMap, freshAxioms.values.toSet)
        
        // Solve Equations, giving substitution from fresh theory to general theory
        val sortSubstitution = Unification.unify(equations.toList)
        
        // Create new signature and terms using substitution
        val newConstants: Set[AnnotatedVar] = theory.constantDeclarations map (av => {
            Var(av.name) of sortSubstitution(constantMap(av.name))
        })
        
        val newFunctions: Set[FuncDecl] = theory.functionDeclarations map (f => {
            val (argSorts, resSort) = fnMap(f.name)
            val newArgSorts: Seq[Sort] = argSorts map sortSubstitution
            val newResSort = sortSubstitution(resSort)
            FuncDecl(f.name, newArgSorts, newResSort)
        })
        
        // Maps original theory axiom to general axiom 
        val generalAxioms: Map[Term, Term] = for((originAx, freshAx) <- freshAxioms) yield (originAx -> sortSubstitution(freshAx))
        
        val usedSorts: Set[Sort] = (0 to (freshSubstitution.index - 1)).map(sortVar(_)).map(sortSubstitution(_)).toSet
        
        val generalTheory = Theory.empty
            .withSorts(usedSorts.toSeq : _*)
            .withConstantDeclarations(newConstants)
            .withFunctionDeclarations(newFunctions)
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