package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.operations.TermOps._
import java.lang.IllegalArgumentException
import fortress.util.Errors

// Skolemizes a given term, which must be in negation normal form.
// Free variables in the given term are ignored, so the top level term must be
// closed with respect to the signature in question for this operation to be valid.

/** Creates a Skolemizer primed to Skolemize the given topLevelTerm.
* When creating new skolem functions or constants, and also when introducing
* new variables while making substitutions (@see Substituter), the provided
* name generator will be used.
* This will mutate the name generator.
*/
class Skolemizer(topLevelTerm: Term, signature: Signature, nameGen: NameGenerator) {
    val skolemFunctions = scala.collection.mutable.Set[FuncDecl]()
    val skolemConstants = scala.collection.mutable.Set[AnnotatedVar]()
    val visitor = new SkolemVisitor
    
    /**
    * Perform the skolemization and get the resulting term.
    * Don't forget to call getSkolemFunctions() and getSkolemConstants()
    * after this.
    * Convert should only be called once per Skolemizer object.
    */
    def convert(): Term = {
        visitor.visit(topLevelTerm)
    }
    
    /** Returns the set of generated skolem functions. Must be called after convert. */
    def getSkolemFunctions: Set[FuncDecl] = skolemFunctions.toSet
    
    /** Returns the set of generated skolem functions. Must be called after convert. */
    def getSkolemConstants: Set[AnnotatedVar] =  skolemConstants.toSet
    
    class SkolemVisitor extends TermVisitorWithTypeContext[Term](signature) {
        
        override def visitTop: Term = Top
        
        override def visitBottom: Term = Bottom
        
        override def visitVar(variable: Var): Term = variable
        
        override def visitNot(term: Not): Term = term.mapBody(visit)
        
        override def visitAndList(term: AndList): Term = term.mapArguments(visit)
        
        override def visitOrList(term: OrList): Term = term.mapArguments(visit)
        
        override def visitDistinct(term: Distinct): Term =
            throw new IllegalArgumentException("Term supposed to be in NNF but found distinct: " + term.toString)
        
        override def visitIff(term: Iff): Term =
            throw new IllegalArgumentException("Term supposed to be in NNF but found iff: " + term.toString)
        
        override def visitImplication(term: Implication): Term =
            throw new IllegalArgumentException("Term supposed to be in NNF but found imp: " + term.toString)
        
        override def visitEq(term: Eq): Term = term.mapArguments(visit)
        
        override def visitApp(term: App): Term = term.mapArguments(visit)
        
        override def visitBuiltinApp(term: BuiltinApp): Term = term.mapArguments(visit)
        
        override def visitExistsInner(term: Exists): Term = {
            var temporaryBody = term.body
            for(av <- term.vars) {
                // To determine what arguments the skolem function needs, look at the
                // free variables of (Exists x body), and see which of them are universally 
                // quantified earlier (which also means we discard constants, unless they are shadowed)
                // Note that since we remove existential quantifiers from the top down,
                // any variable on the stack is universally quantified
                val skolemArguments: Seq[AnnotatedVar] = for {
                    variable <- term.freeVarConstSymbols.toList
                    annotatedVar <- mostRecentStackAppearence(variable)
                } yield annotatedVar

                if(skolemArguments.size == 0) {
                    // Skolem constant
                    val skolemConstantName = nameGen.freshName("sk")
                    
                    val skolemConstant = Var(skolemConstantName) of av.sort
                    skolemConstants += skolemConstant
                    
                    temporaryBody = temporaryBody.substitute(av.variable, skolemConstant.variable)
                    
                    // We also have to update the signature with the new skolem constant
                    // since it might now appear deeper in the new term
                    // Failing to do this was a former bug
                    signature = signature.withConstant(skolemConstant);
                } else {
                    // Skolem function
                    val skolemFunctionName = nameGen.freshName("sk")
                    
                    val argumentSorts = skolemArguments.map(_.sort)
                    val arguments = skolemArguments.map(_.variable)
                    
                    val skolemFunction = FuncDecl(skolemFunctionName, argumentSorts, av.sort)
                    skolemFunctions += skolemFunction
                    
                    val skolemApplication = App(skolemFunctionName, arguments)
                    temporaryBody = temporaryBody.substitute(av.variable, skolemApplication, nameGen)
                    
                    signature = signature.withFunctionDeclaration(skolemFunction)
                }
            }
            visit(temporaryBody)
        }
        
        override def visitForallInner(term: Forall): Term = term.mapBody(visit)
        
        override def visitDomainElement(d: DomainElement): Term = d
        
        override def visitIntegerLiteral(literal: IntegerLiteral): Term = literal
        
        override def visitBitVectorLiteral(literal: BitVectorLiteral): Term = literal
        
        override def visitEnumValue(e: EnumValue): Term = e
        
        override def visitIfThenElse(ite: IfThenElse): Term = {
            // Note that we assume ite conditions do not contain quantifiers
            IfThenElse(ite.condition, visit(ite.ifTrue), visit(ite.ifFalse))
        }
    }
}
