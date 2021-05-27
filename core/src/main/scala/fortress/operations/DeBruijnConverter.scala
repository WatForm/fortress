package fortress.operations

import fortress.msfol._

case class DeBruijnMapping(index: Int, variable: Var)

/** Converts the variables in a term into a standardized DeBruijn Form.
  * We use this to check that substitution works correctly, but don't actually
  * use DeBruijn form within Fortress. */
class DeBruijnConverter {
    private var counter: Int = 0;
    private var mappingStack = List.empty[DeBruijnMapping]
    private val visitor = new DeBruijnVisitor
    
    def convert(term: Term) = visitor.visit(term)
    
    class DeBruijnVisitor extends TermVisitor[Term] {
        
        override def visitTop(): Term = Top
        
        override def visitBottom(): Term = Bottom
        
        override def visitVar(variable: Var): Term = {
            for(m <- mappingStack) {
                if(variable == m.variable) {
                    return Var("_" + Integer.toString(m.index))
                }
            }
            variable
        }
        
        override def visitNot(term: Not): Term = term.mapBody(visit)
        
        override def visitAndList(term: AndList): Term = term.mapArguments(visit)
        
        override def visitOrList(term: OrList): Term = term.mapArguments(visit)
        
        override def visitDistinct(term: Distinct): Term = term.mapArguments(visit)
        
        override def visitImplication(term: Implication): Term = term.mapArguments(visit)
        
        override def visitIff(term: Iff): Term = term.mapArguments(visit)
        
        override def visitEq(term: Eq): Term = term.mapArguments(visit)
        
        override def visitApp(term: App): Term = term.mapArguments(visit)
        
        override def visitBuiltinApp(term: BuiltinApp) = term.mapArguments(visit)

        override def visitClosure(term: Closure) = term.mapArguments(visit)

        override def visitReflexiveClosure(term: ReflexiveClosure) = term.mapArguments(visit)

        private def pushVar(av: AnnotatedVar): Unit = {
            counter += 1
            val m = DeBruijnMapping(counter, av.variable)
            mappingStack = m :: mappingStack
        }
        
        private def popVar(): Unit = {
            counter -= 1
            mappingStack = mappingStack.tail
        }
        
        override def visitExists(term: Exists): Term = {
            val newVars = term.vars.map(av => {
                pushVar(av)
                Var("_" + Integer.toString(counter)) of av.sort
            })
            
            val body = visit(term.body)
            
            // Return state back to way it was
            term.vars.foreach(av => popVar())
            
            Exists(newVars, body)
        }
        
        override def visitForall(term: Forall): Term = {
            val newVars = term.vars.map(av => {
                pushVar(av)
                Var("_" + Integer.toString(counter)) of av.sort
            })
            
            val body = visit(term.body)
            
            // Return state back to way it was
            term.vars.foreach(av => popVar())
            
            Forall(newVars, body)
        }
        
        override def visitDomainElement(d: DomainElement): Term = ???
        
        override def visitIntegerLiteral(literal: IntegerLiteral): Term = ???
        
        override def visitBitVectorLiteral(literal: BitVectorLiteral): Term = ???
        
        override def visitEnumValue(e: EnumValue): Term = ???
        
        override def visitIfThenElse(ite: IfThenElse): Term = ???
        
    }
    
}
