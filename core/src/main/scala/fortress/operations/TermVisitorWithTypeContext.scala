package fortress.operations

import fortress.msfol._
import fortress.util.Errors

abstract class TermVisitorWithTypeContext[T](protected var signature: Signature) extends TermVisitor[T] {
    private var typeContextStack: List[AnnotatedVar] = List.empty
    private var typeContextStackFuncDecls: List[FuncDecl] = List.empty
    
    // // For entering partway through a term traversal
    // protected TermVisitorWithTypeContext(Signature signature, Deque<AnnotatedVar> sortContextStack) {
    //     this.signature = signature;
    //     this.typeContextStack = typeContextStack;
    // }
    
    // Looks up variable sort in context first, then tries constants
    protected def lookupSort(variable: Var): Option[Sort] = {
        // Check if it is in the Context
        // Note that the context is used as a stack, so we just need to iterate
        // from front to back and not have to worry about shadowed variables.
        // e.g. in (forall v: A, forall v : B, p(v)), the context will look like
        // List[v: B, v: A], and the term will fail to typecheck if p : A -> Bool
        // since the use of v will have type B
        typeContextStack.find(_.name == variable.name)
            .orElse(signature.getAnnotatedVarOfConstant(variable))
            // Gives Option[AnnotatedVar] so far. Take .sort
            .map(_.sort)
    }

    protected def lookupFuncDecl(name: String): Option[FuncDecl] = {
        typeContextStackFuncDecls.find(_.name == name)
            .orElse(signature.queryFunctionDeclaration(name))
            .orElse(signature.queryFunctionDefinition(name).map(_.asDeclWithoutBody))
    }
    
    
    protected def visitForallInner(forall: Forall): T
    protected def visitExistsInner(exists: Exists): T

    protected def visitForall2ndOrderInner(forall: Forall2ndOrder): T
    protected def visitExists2ndOrderInner(exists: Exists2ndOrder): T

    //protected def visitDefnBody(t:Term): T

    protected def mostRecentStackAppearence(variable: Var): Option[AnnotatedVar] = typeContextStack.find(_.name == variable.name)
    
    final override def visitForall(forall: Forall): T = {
        // Must put variables on context stack in this order
        // e.g. (forall v: A v: B, p(v)), the context should be
        // List[v: B, v: A]
        for(av <- forall.vars) {
            typeContextStack = av :: typeContextStack
        }
        
        val result: T = visitForallInner(forall)
        
        // Pop context stack
        for(av <- forall.vars) {
            typeContextStack = typeContextStack.tail
        }
        
        result
    }
    
    final override def visitExists(exists: Exists): T = {
        // Must put variables on context stack in this order
        // e.g. (forall v: A v: B, p(v)), the context should be
        // List[v: B, v: A]
        for(av <- exists.vars) {
            typeContextStack = av :: typeContextStack
        }
        
        val result: T = visitExistsInner(exists)
        
        // Pop context stack
        for(av <- exists.vars) {
            typeContextStack = typeContextStack.tail
        }
        
        result
    }
    
    final override def visitExists2ndOrder(exists: Exists2ndOrder): T = {
        // Push onto context stack
        for(av <- exists.declarations) {
            typeContextStackFuncDecls = av :: typeContextStackFuncDecls
        }
        
        val result: T = visitExists2ndOrderInner(exists)

        // Pop context stack
        typeContextStackFuncDecls = typeContextStackFuncDecls.drop(exists.declarations.length)
        
        result
    }

    final override def visitForall2ndOrder(forall: Forall2ndOrder): T = {
        
        // Push onto context stack
        for(av <- forall.declarations) {
            typeContextStackFuncDecls = av :: typeContextStackFuncDecls
        }
        
        val result: T = visitForall2ndOrderInner(forall)

        // Pop context stack
        typeContextStackFuncDecls = typeContextStackFuncDecls.drop(forall.declarations.length)
        
        result
    }

    def visitDefn(t: Term, vars: Seq[AnnotatedVar]): T = {
        // Must put variables on context stack in this order
        // e.g. (forall v: A v: B, p(v)), the context should be
        // List[v: B, v: A]
        for(av <- vars) {
            typeContextStack = av :: typeContextStack
        }
        
        val result: T = visit(t)
        
        // Pop context stack
        for(av <- vars) {
            typeContextStack = typeContextStack.tail
        }
        
        result
    }
}
