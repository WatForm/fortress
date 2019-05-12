package fortress.solverinterface

import com.microsoft.z3.{
    Context => Z3Context,
    Solver => Z3Solver,
    Sort => Z3Sort,
    FuncDecl => Z3FuncDecl,
    Expr => Z3Expr,
    BoolExpr => Z3BoolExpr
}

import fortress.msfol._
import fortress.msfol.operations.TermVisitorWithTypeContext

import scala.collection.JavaConverters._

// Precondition: theory must be typechecked and all declarations must
// be internally consistent
class TheoryToZ3Java(theory: Theory) {
    
    val termVisitor = new TermToZ3Visitor
    val config = Map(
        "model" -> "true" // How does this affect performance?
    )
    val context = new Z3Context(config.asJava);
    
    val sortConversions: Map[Sort, Z3Sort] = {
        val tuples = for(t <- theory.sorts if ! t.isBuiltin) yield {
            (t, context.mkUninterpretedSort(t.name))
        }
        tuples.toMap + (BoolSort -> context.getBoolSort)
    }
    
    val constantConversions: Map[String, Z3FuncDecl] = {
        val tuples = for(constant <- theory.constants) yield {
            val z3Sort = sortConversions(constant.sort)
            val z3Decl = context.mkConstDecl(constant.name, z3Sort)
            (constant.name, z3Decl)
        }
        tuples.toMap
    }
    
    val functionConversions: Map[String, Z3FuncDecl] = {
        val tuples = for(fdecl <- theory.functionDeclarations) yield {
            val z3ArgSorts: Array[Z3Sort] = fdecl.argSorts.map(sortConversions).toArray
            val z3ResultSort = sortConversions(fdecl.resultSort)
            val z3Decl = context.mkFuncDecl(fdecl.name, z3ArgSorts, z3ResultSort)
            (fdecl.name, z3Decl)
        }
        tuples.toMap
    }
    
    def convert: (Z3Context, Z3Solver) = {
        val solver  = context.mkSolver("QF_UF") // How does changing the logic affect the efficiency?
        
        for(axiom <- theory.axioms) {
            val formula: Z3BoolExpr = termVisitor.visit(axiom).asInstanceOf[Z3BoolExpr]
            solver.add(formula)
        }
        
        (context, solver)
    }
    
    class TermToZ3Visitor extends TermVisitorWithTypeContext[Z3Expr](theory.signature) {
        
        override def visitTop(): Z3Expr = context.mkTrue()
        
        override def visitBottom(): Z3Expr = context.mkFalse()
        
        override def visitVar(variable: Var): Z3Expr = {
            val z3Sort = sortConversions(lookupSort(variable).get)
            context.mkConst(variable.name, z3Sort)
        }
        
        override def visitNot(term: Not): Z3Expr = {
            val body = visit(term.body).asInstanceOf[Z3BoolExpr]
            context.mkNot(body)
        }
        
        override def visitAndList(term: AndList): Z3Expr = {
            val args = term.arguments.map(arg => visit(arg).asInstanceOf[Z3BoolExpr])
            return context.mkAnd(args:_*)
        }
        
        override def visitOrList(term: OrList): Z3Expr = {
            val args = term.arguments.map(arg => visit(arg).asInstanceOf[Z3BoolExpr])
            return context.mkOr(args:_*)
        }
        
        override def visitDistinct(term: Distinct): Z3Expr = {
            val args = term.arguments.map(visit)
            context.mkDistinct(args:_*)
        }
        
        override def visitImplication(term: Implication): Z3Expr =
            context.mkImplies(
                visit(term.left).asInstanceOf[Z3BoolExpr],
                visit(term.right).asInstanceOf[Z3BoolExpr]
            )
        
        override def visitIff(term: Iff): Z3Expr =
            context.mkEq(visit(term.left), visit(term.right)) // Z3 uses Eq for Iff
        
        override def visitEq(term: Eq): Z3Expr =
            context.mkEq(visit(term.left), visit(term.right))
        
        override def visitApp(term: App): Z3Expr = {
            val z3Decl = functionConversions(term.functionName)
            val args = term.arguments.map(visit)
            z3Decl.apply(args:_*)
        }
        
        override def visitExistsInner(term: Exists): Z3Expr = {
            // TODO will having no patterns change performance?
            // TODO look at C++ docs if Java docs doesn't have the info
            val vars: Array[Z3Expr] = term.vars.map(av => visit(av.variable)).toArray
            val body = visit(term.body)
            context.mkExists(
                vars,
                body,
                0, // Default weight of 0
                null, // No patterns
                null, // No anti-patterns
                null, // No symbol to track quantifier
                null // No symbol to track skolem constants
            )
        }
        
        override def visitForallInner(term: Forall): Z3Expr = {
            // TODO will having no patterns change performance?
            // TODO look at C++ docs if Java docs doesn't have the info
            val vars: Array[Z3Expr] = term.vars.map(av => visit(av.variable)).toArray
            val body = visit(term.body)
            context.mkForall(
                vars,
                body,
                0, // Default weight of 0
                null, // No patterns
                null, // No anti-patterns
                null, // No symbol to track quantifier
                null // No symbol to track skolem constants
            )
        }
        
        override def visitDomainElement(d: DomainElement): Z3Expr = ???
        
        override def visitIntegerLiteral(literal: IntegerLiteral): Z3Expr = ???
        
        override def visitBitVectorLiteral(literal: BitVectorLiteral): Z3Expr = ???
        
        override def visitEnumValue(e: EnumValue): Z3Expr = ???
    }
}
