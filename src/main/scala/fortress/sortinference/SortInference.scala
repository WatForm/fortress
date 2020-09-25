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
        val constantMap: Map[String, Sort] = theory.constants.map {c => c.name -> freshSubstitution(c).sort}.toMap
        
        // Associate each function with a collection of fresh sorts
        val fnMap: Map[String, (Seq[Sort], Sort)] = theory.functionDeclarations.map { f => {
            val f_sub = freshSubstitution(f)
            f.name -> (f_sub.argSorts, f_sub.resultSort)
        }}.toMap
        
        val replacedAxioms = theory.axioms map freshSubstitution
        
        // Gather equations
        val equations: Set[Equation] = Equation.accumulate(constantMap, fnMap, replacedAxioms)
        
        // Solve Equations
        val sortSubstitution = Unification.unify(equations.toList)
        
        // Create new signature and terms using substitution
        val newConstants: Set[AnnotatedVar] = theory.constants map (av => {
            Var(av.name) of sortSubstitution(constantMap(av.name))
        })
        
        val newFunctions: Set[FuncDecl] = theory.functionDeclarations map (f => {
            val (argSorts, resSort) = fnMap(f.name)
            val newArgSorts: Seq[Sort] = argSorts map sortSubstitution
            val newResSort = sortSubstitution(resSort)
            FuncDecl(f.name, newArgSorts, newResSort)
        })
        
        val newAxioms: Set[Term] = replacedAxioms map sortSubstitution
        
        val usedSorts: Set[Sort] = (0 to (freshSubstitution.index - 1)).map(sortVar(_)).map(sortSubstitution(_)).toSet
        
        val generalTheory = Theory.empty
            .withSorts(usedSorts.toSeq : _*)
            .withConstants(newConstants)
            .withFunctionDeclarations(newFunctions)
            .withAxioms(newAxioms)
        
        val substitution = SortSubstitution.computeSigMapping(generalTheory.signature, theory.signature)
        
        // If the substitution does nothing except rename sorts (i.e. sort inference did nothing)
        // then just return the original theory
        // Otherwise, return the more general inferred theory
        if(substitution.isBijectiveRenaming)
            (theory, SortSubstitution.identity)
        else (generalTheory, substitution)
    }
    
}