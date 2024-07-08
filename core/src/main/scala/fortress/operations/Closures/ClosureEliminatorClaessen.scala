package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.problemstate._
import fortress.util.Errors

import java.lang.IllegalArgumentException
import java.util.ArrayList
import scala.jdk.CollectionConverters._

class ClosureEliminatorClaessen(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {

    override val visitor = new ClosureVisitorCleassen

    def nameFunctionS(functionName: String): String = "^" + functionName + "^s"
    def nameFunctionC(functionName: String): String = "^" + functionName + "^C" 


    class ClosureVisitorCleassen extends ClosureVisitor {
        def defineReflexiveClosure(sort: Sort, functionName: String) = {
            // Auxilary functions
            val s = nameFunctionS(functionName)
            val C = nameFunctionC(functionName)
            val reflexiveClosureName = getReflexiveClosureName(functionName)

            val fixedSorts: Seq[Sort] = getFixedSorts(functionName)

            auxilaryFunctions += FuncDecl(s, Seq(sort, sort) ++ fixedSorts, sort)
            auxilaryFunctions += FuncDecl(C, Seq(sort, sort, sort) ++ fixedSorts, Sort.Bool)
            closureFunctions += FuncDecl(reflexiveClosureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)

            val x = Var("x")
            val y = Var("y")
            val z = Var("z")
            val u = Var("u")

            val fixedVars = getFixedVars(fixedSorts.length)
            val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))

            closureAxioms += Forall(Seq(x,y,z,u).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    And(App(C, Seq(x, y, u) ++ fixedVars), App(C, Seq(y, z, u) ++ fixedVars)),
                    App(C, Seq(x, z, u) ++ fixedVars)
                )
            )
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)) ++ fixedArgVars, Not(App(C, Seq(x, x, y) ++ fixedVars)))
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    And(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), Not(Eq(x, y))),
                    App(C, Seq(x, App(s, Seq(x, y) ++ fixedVars), y) ++ fixedVars)
                )
            )
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    And(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), Not(Eq(x, y))),
                    App(reflexiveClosureName, Seq(App(s, Seq(x, y) ++ fixedVars), y) ++ fixedVars)
                )
            )
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    And(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), Not(Eq(x, y))),
                    funcContains(functionName, x, App(s, Seq(x, y) ++ fixedVars), fixedVars)
                )
            )
            closureAxioms += Forall(Seq(x,y,z).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    And(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), App(reflexiveClosureName, Seq(y, z) ++ fixedVars)),
                    App(reflexiveClosureName, Seq(x, z) ++ fixedVars)
                )
            )
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    funcContains(functionName, x, y, fixedVars),
                    App(reflexiveClosureName, Seq(x, y) ++ fixedVars)
                )
            )
            closureAxioms += Forall(Seq(x.of(sort)) ++ fixedArgVars, App(reflexiveClosureName, Seq(x, x) ++ fixedVars))
        }

        def visitReflexiveClosure(rc: ReflexiveClosure): Term = {
            val reflexiveClosureName = getReflexiveClosureName(rc.functionName)
            // Find the sort we are closing over
            val sort = getClosingSortOfFunction(rc.functionName)
            if (!queryFunction(reflexiveClosureName)){
                defineReflexiveClosure(sort, rc.functionName)
            }

            App(reflexiveClosureName, Seq(rc.arg1, rc.arg2) ++ rc.fixedArgs).mapArguments(visit)
        }

        def visitClosure(c: Closure): Term = {
            val closureName = getClosureName(c.functionName)
            val reflexiveClosureName = getReflexiveClosureName(c.functionName)
            // Find the sort we are closing over
            val sort = getClosingSortOfFunction(c.functionName)

            if (!queryFunction(closureName)){
                if (!queryFunction(reflexiveClosureName)){
                    defineReflexiveClosure(sort, c.functionName)
                }
                val fixedSorts = getFixedSorts(c.functionName)
                val fixedVars = getFixedVars(fixedSorts.length)
                val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))
                closureFunctions += FuncDecl(closureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                val x = Var("x")
                val y = Var("y")
                val z = Var("z")
                closureAxioms += Forall(Seq(x, y).map(_.of(sort)) ++ fixedArgVars, Iff(
                    App(closureName, Seq(x, y) ++ fixedVars),
                    Exists(z.of(sort), 
                        And(
                            funcContains(c.functionName, x, z, fixedVars),
                            App(reflexiveClosureName, Seq(z, y) ++ fixedVars)
                        )
                    )
                ))
            }
            


            App(closureName, Seq(c.arg1, c.arg2) ++ c.fixedArgs).mapArguments(visit)
        }
    }
  
}
