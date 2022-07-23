package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.util.Errors
import java.lang.IllegalArgumentException
import java.util.ArrayList

import scala.jdk.CollectionConverters._

/** Removes closure given a term, which must be in negation normal form.
  * Free variables in the given term are ignored, so the top level term must be
  * closed with respect to the signature in question for this operation to be valid.
  */
abstract class ClosureEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, (Int, Boolean)], nameGen: NameGenerator) {

    // All closure functions we have generated (helps to avoid duplicates)
    val closureFunctions = scala.collection.mutable.Set[FuncDecl]()
    // Generated axioms
    val closureAxioms = scala.collection.mutable.Set[Term]()

    val visitor: ClosureVisitor

    /** Returns the set of generated closure functions. Must be called after convert. */
    def getClosureFunctions: Set[FuncDecl] = closureFunctions.toSet
    
    /** Returns the set of generated skolem functions. Must be called after convert. */
    def getClosureAxioms: Set[Term] =  closureAxioms.toSet

    /**
    * Perform the closure elimination and get the resulting term.
    * Don't forget to call getClosureFunctions() and getClosureAxioms()
    * after this.
    * Convert should only be called once per ClosureEliminator object.
    */
    def convert(): Term = {
        visitor.visit(topLevelTerm)
    }

    abstract class ClosureVisitor extends TermVisitorWithTypeContext[Term](signature) {

        def queryFunction(name: String): Boolean = signature.hasFunctionWithName(name) || closureFunctions.exists(f => f.name == name)
        def getReflexiveClosureName(name: String, idx: String = ""): String = "*" + idx + name
        def getClosureName(name: String, idx: String = ""): String = "^" + idx + name
        
        def visitTop: Term = Top
        
        def visitBottom: Term = Bottom
        
        def visitVar(variable: Var): Term = variable
        
        def visitNot(term: Not): Term = term.mapBody(visit)
        
        def visitAndList(term: AndList): Term = term.mapArguments(visit)
        
        def visitOrList(term: OrList): Term = term.mapArguments(visit)
        
        def visitDistinct(term: Distinct): Term = term.mapArguments(visit)
        
        def visitIff(term: Iff): Term = term.mapArguments(visit)
        
        def visitImplication(term: Implication): Term = term.mapArguments(visit)
        
        def visitEq(term: Eq): Term = term.mapArguments(visit)
        
        def visitApp(term: App): Term = term.mapArguments(visit)
        
        def visitBuiltinApp(term: BuiltinApp): Term = term.mapArguments(visit)

        // defined specifically for closure elim method
        def visitClosure(c: Closure): Term

        // defined specifically for closure elim method
        def visitReflexiveClosure(rc: ReflexiveClosure): Term

        def visitForallInner(term: Forall): Term = term.mapBody(visit)
        
        def visitExistsInner(term: Exists): Term = term.mapBody(visit)
        
        def visitDomainElement(d: DomainElement): Term = d
        
        def visitIntegerLiteral(literal: IntegerLiteral): Term = literal
        
        def visitBitVectorLiteral(literal: BitVectorLiteral): Term = literal
        
        def visitEnumValue(e: EnumValue): Term = e

        def visitIfThenElse(ite: IfThenElse): Term = IfThenElse(visit(ite.condition), visit(ite.ifTrue), visit(ite.ifFalse))
    }
}