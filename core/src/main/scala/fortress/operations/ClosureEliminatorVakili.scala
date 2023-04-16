package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.problemstate._
import fortress.util.Errors

import java.lang.IllegalArgumentException
import java.util.ArrayList
import scala.jdk.CollectionConverters._

class ClosureEliminatorVakili(topLevelTerm: Term, allowedRelations: Set[String], signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {
    override val visitor = new ClosureVisitorVakili

    class ClosureVisitorVakili extends ClosureVisitor {

        // closure and reflexive closure is unchanged. We want NOT(Closure....)
        def visitReflexiveClosure(rc: ReflexiveClosure): Term = rc

        def visitClosure(c: Closure): Term = c

        def createClosure(functionName: String): Unit = {
            // get the sort we close over
            val rel = signature.queryFunctionDeclaration(functionName).get
            val sort = rel.argSorts(0)
            
            val closureName = getClosureName(functionName)
            val fixedSorts = getFixedSorts(functionName)
            // Declare the closure function
            closureFunctions += FuncDecl(closureName, sort +: sort +: fixedSorts, BoolSort)
            // closure is simply defined to include everything in f and to be reflexive
            val x = Var(nameGen.freshName("x"))
            val y = Var(nameGen.freshName("y"))
            val z = Var(nameGen.freshName("z"))
            val axy = List(x.of(sort), y.of(sort))

            val fixedVars = getFixedVars(fixedSorts.length)
            val fixedArgVars = getFixedAVars(functionName)
            
            closureAxioms += Forall(axy ++ fixedArgVars,
                Iff(
                    App(closureName, x +: y +: fixedVars),
                    Or(
                        App(functionName, x +: y +: fixedVars),
                        Exists(z.of(sort),
                            And(
                                App(functionName, x +: z +: fixedVars),
                                App(closureName, z +: y +: fixedVars)
                            )
                        )
                    )
                )
            )
        }

        def createReflexiveClosure(functionName: String): Unit = {
            val closureName = getClosureName(functionName)
            if (!queryFunction(closureName)){
                createClosure(functionName)
            }

            val rel = signature.queryFunctionDeclaration(functionName).get
            val sort = rel.argSorts(0)

            val reflexiveClosureName = getReflexiveClosureName(functionName)
            val fixedSorts = getFixedSorts(functionName)
            // Declare the closure function
            closureFunctions += FuncDecl(reflexiveClosureName, sort +: sort +: fixedSorts, BoolSort)
            // closure is simply defined to include everything in f and to be reflexive
            val x = Var(nameGen.freshName("x"))
            val y = Var(nameGen.freshName("y"))
            val z = Var(nameGen.freshName("z"))
            val axy = List(x.of(sort), y.of(sort))

            val fixedVars = getFixedVars(fixedSorts.length)
            val fixedArgVars = getFixedAVars(functionName)

            // R* = R^ union {(x,x) | x in sort }
            closureAxioms += Forall(axy,
                Iff(
                    App(reflexiveClosureName, x +: y +: fixedVars),
                    Or(
                        Eq(x, y),
                        App(closureName, x +: y +: fixedVars)
                    )
                )
                
            )

        }

        override def visitNot(n: Not): Term = n match {
            case Not(Closure(fname, start, end, fixedArgs)) if allowedRelations.contains(fname) => {
                // create transitive closure if it does not exist
                val closureName = getClosureName(fname)
                if(!queryFunction(closureName)){
                    createClosure(fname)
                }
                Not(App(closureName, start +: end +: fixedArgs))
            }
            case Not(ReflexiveClosure(fname, start, end, fixedArgs)) if allowedRelations.contains(fname) => {
                // create reflexive closure if it does not exist
                val reflexiveClosureName = getReflexiveClosureName(fname)
                if (!queryFunction(reflexiveClosureName)){
                    createReflexiveClosure(fname)
                }

                Not(App(reflexiveClosureName, start +: end +: fixedArgs))
            }
            case Not(t) => Not(t)
        }
    }
  
}
