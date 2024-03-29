package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.problemstate._
import fortress.util.Errors

import java.lang.IllegalArgumentException
import java.util.ArrayList
import scala.jdk.CollectionConverters._

/** Removes closure given a term, which must be in negation normal form.
  * Free variables in the given term are ignored, so the top level term must be
  * closed with respect to the signature in question for this operation to be valid.
  */
abstract class ClosureEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator) {

    // All closure functions we have generated (helps to avoid duplicates)
    val closureFunctions = scala.collection.mutable.Set[FuncDecl]()
    // Generated axioms
    val auxilaryFunctions = scala.collection.mutable.Set[FuncDecl]()
    val closureAxioms = scala.collection.mutable.Set[Term]()

    val visitor: ClosureVisitor

    /** Returns the set of generated closure functions. Must be called after convert. */
    def getClosureFunctions: Set[FuncDecl] = closureFunctions.toSet
    
    def getAuxilaryFunctions: Set[FuncDecl] = auxilaryFunctions.toSet

    /** Returns the set of generated closure axioms. Must be called after convert. */
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

    // All visit (reflexive)Closure functions should return an app with (reflexive)ClosureName
    def getReflexiveClosureName(name: String, idx: String = ""): String = "*" + idx + name
    def getClosureName(name: String, idx: String = ""): String = "^" + idx + name

    abstract class ClosureVisitor extends TermVisitorWithTypeContext[Term](signature) {

        def queryFunction(name: String): Boolean = signature.hasFuncDeclWithName(name) || closureFunctions.exists(f => f.name == name) || auxilaryFunctions.exists(_.name == name)

        def getFixedVars(numArgs: Int): Seq[Var] = for (n: Int <- 0 to numArgs - 1) yield Var("fa"+ n.toString())

        def funcContains(fname: String, x: Term, y: Term, arguments: Seq[Term]): Term = {
            val fdecl = signature.functionWithName(fname) match {
                case Some(fdecl) => fdecl
                //Default to just including the arguments
                case None => return App(fname, Seq(x, y) ++ arguments)
            }
            
            // Depending on arity, we check membership differently
            fdecl.arity match {
                // We ignore arguments even if we take them in for the case of arity 1 or 2 so that we can leave them in for iterative methods
                case 1 => Eq(App(fname, x), y)
                case 2 => App(fname, x, y)
                case arity => {
                    // We currently assume closing non-binary relations close over arguments 0 and 1
                    Errors.Internal.precondition(arity == arguments.length + 2, 
                        "Closing over a function of arity " + arity.toString() + "but arguments was length " + arguments.length.toString() + "instead of " + (arity-2).toString())
                    App(fname, Seq[Term](x, y) ++ arguments)
                }
            }
        }

        // Gets the sorts for fixed arguments (everything after the first 2 args)
        def getFixedSorts(fname: String): Seq[Sort] = signature.queryFunctionDeclaration(fname) match {
            case None => Errors.Internal.impossibleState("Function " + fname + " does not exist when closing over it!")
            case Some(FuncDecl(_, sorts, _)) => sorts.drop(2).toList
        }

        def getFixedAVars(fname: String): Seq[AnnotatedVar] = {
            val fixedSorts = getFixedSorts(fname)
            fixedSorts.zipWithIndex.map {
                case (sort, n) =>
                    AnnotatedVar(Var("fa" + n.toString()), sort)
            }
        }
        
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