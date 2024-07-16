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
    val closureDefns = scala.collection.mutable.Set[FunctionDefinition]()
    // Generated axioms
    val auxilaryFunctions = scala.collection.mutable.Set[FuncDecl]()
    val auxilaryDefns = scala.collection.mutable.Set[FunctionDefinition]()
    val closureAxioms = scala.collection.mutable.Set[Term]()

    // Sorts that must be made unchanging. Used by iterative closure elimiators.
    val unchangingSorts = scala.collection.mutable.Set[Sort]()

    val visitor: ClosureVisitor

    /** Returns the set of generated closure functions. Must be called after convert. */
    def getClosureFunctions: Set[FuncDecl] = closureFunctions.toSet

    def getClosureDefns: Set[FunctionDefinition] = closureDefns.toSet
    
    def getAuxilaryFunctions: Set[FuncDecl] = auxilaryFunctions.toSet

    def getAuxilaryDefns: Set[FunctionDefinition] = auxilaryDefns.toSet

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

        def queryFunction(name: String): Boolean = signature.hasFuncDeclWithName(name) ||
            closureFunctions.exists(_.name == name) ||
            closureDefns.exists(_.name == name) ||
            auxilaryFunctions.exists(_.name == name) ||
            auxilaryDefns.exists(_.name == name)

        // Creates variables to represent `numArgs` additional "fixed" variables
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
        def getFixedSorts(fname: String): Seq[Sort] = signature.queryFunction(fname) match {
            case None => Errors.Internal.impossibleState("Function " + fname + " does not exist in signature when closing over it!")
            case Some(Left(FuncDecl(_, sorts, _))) => sorts.drop(2).toList
            case Some(Right(FunctionDefinition(_, params, _, _))) => params.map(_.sort).drop(2).toList
        }

        def getClosingSortOfFunction(fname: String): Sort = signature.queryFunction(fname) match {
            case None => Errors.Internal.impossibleState(f"Could not find ${fname} when closing over it")
            case Some(func) => func match {
                case Left(fdef) => fdef.argSorts(0)
                case Right(fdec) => fdec.argSorts(0)
            }
        }

        // Gets annotated variables for the fixed arguments
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