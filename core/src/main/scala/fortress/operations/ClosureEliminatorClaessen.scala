package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.util.Errors
import java.lang.IllegalArgumentException
import java.util.ArrayList

import scala.jdk.CollectionConverters._

class ClosureEliminatorClaessen(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Int], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {

    override val visitor = new ClosureVisitorCleassen

    def nameFunctionS(functionName: String): String = "^" + functionName + "^s"
    def nameFunctionC(functionName: String): String = "^" + functionName + "^C" 


    class ClosureVisitorCleassen extends ClosureVisitor {
        def defineReflexiveClosure(sort: Sort, functionName: String) = {
            val s = nameFunctionS(functionName)
            val C = nameFunctionC(functionName)
            val reflexiveClosureName = getReflexiveClosureName(functionName)
            closureFunctions += FuncDecl(s, sort, sort, sort)
            closureFunctions += FuncDecl(C, sort, sort, sort, Sort.Bool)
            closureFunctions += FuncDecl(reflexiveClosureName, sort, sort, Sort.Bool)

            val x = Var("x")
            val y = Var("y")
            val z = Var("z")
            val u = Var("u")

            closureAxioms += Forall(Seq(x,y,z,u).map(_.of(sort)),
                Implication(
                    And(App(C, x, y, u), App(C, y, z, u)),
                    App(C, x, z, u)
                )
            )
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)), Not(App(C, x, x, y)))
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)),
                Implication(
                    And(App(reflexiveClosureName, x, y), Not(Eq(x, y))),
                    App(C, x, App(s, x, y), y)
                )
            )
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)),
                Implication(
                    And(App(reflexiveClosureName, x, y), Not(Eq(x, y))),
                    App(reflexiveClosureName, App(s, x, y), y)
                )
            )
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)),
                Implication(
                    And(App(reflexiveClosureName, x, y), Not(Eq(x, y))),
                    funcContains(functionName, x, App(s, x, y))
                )
            )
            closureAxioms += Forall(Seq(x,y,z).map(_.of(sort)),
                Implication(
                    And(App(reflexiveClosureName, x, y), App(reflexiveClosureName, y, z)),
                    App(reflexiveClosureName, x, z)
                )
            )
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)),
                Implication(
                    funcContains(functionName, x, y),
                    App(reflexiveClosureName, x, y)
                )
            )
            closureAxioms += Forall(x.of(sort), App(reflexiveClosureName, x, x))
        }

        def visitReflexiveClosure(rc: ReflexiveClosure): Term = {
            val reflexiveClosureName = getReflexiveClosureName(rc.functionName)
            val rel = signature.queryUninterpretedFunction(rc.functionName).get
            val sort = rel.argSorts(0)
            if (!queryFunction(reflexiveClosureName)){
                defineReflexiveClosure(sort, rc.functionName)
            }

            App(reflexiveClosureName, Seq(rc.arg1, rc.arg2)).mapArguments(visit)
        }

        def visitClosure(c: Closure): Term = {
            val closureName = getClosureName(c.functionName)
            val reflexiveClosureName = getReflexiveClosureName(c.functionName)
            val rel = signature.queryUninterpretedFunction(c.functionName).get
            val sort = rel.argSorts(0)

            if (!queryFunction(closureName)){
                if (!queryFunction(reflexiveClosureName)){
                    defineReflexiveClosure(sort, c.functionName)
                }
                closureFunctions += FuncDecl(closureName, sort, sort, Sort.Bool)
                val x = Var("x")
                val y = Var("y")
                val z = Var("z")
                closureAxioms += Forall(Seq(x, y).map(_.of(sort)), Iff(
                    App(closureName, x, y),
                    Exists(z.of(sort), 
                        And(
                            funcContains(c.functionName, x, z),
                            App(reflexiveClosureName, z, y)
                        )
                    )
                ))
            }
            


            App(closureName, Seq(c.arg1, c.arg2)).mapArguments(visit)
        }
    }
  
}
