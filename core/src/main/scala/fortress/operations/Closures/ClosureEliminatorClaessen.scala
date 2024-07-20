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
            // Declare some aux functions when cR: TxTx(Fixed...)->Bool
            // s: TxTx(Fixed...)->T
            // s represents the "next step" along the path from the first argument to the second
            auxilaryFunctions += FuncDecl(s, Seq(sort, sort) ++ fixedSorts, sort)
            // C: TxTxTx(Fixed...)->Bool
            // C(a,x,z) is true iff x is closer to z than a is
            auxilaryFunctions += FuncDecl(C, Seq(sort, sort, sort) ++ fixedSorts, Sort.Bool)
            // Add a decl for the reflexive closure
            // R^: TxTx(Fixed...)->Bool
            closureFunctions += FuncDecl(reflexiveClosureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)

            // Variables to use later
            val x = Var("x")
            val y = Var("y")
            val z = Var("z")
            val u = Var("u")

            // build vars and sorted vars for quantifiers for fixed arguments
            val fixedVars = getFixedVars(fixedSorts.length)
            val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))

            // all x,y,z,u: T, fixed...: Fixed... . C(x,y,u, fixed...) & C(y,z,u, fixed...) => C(x,z,u, fixed...)
            // if (y is closer to u than x) and (z is closer to u than y) then (z is closer to u than x)
            closureAxioms += Forall(Seq(x,y,z,u).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    And(App(C, Seq(x, y, u) ++ fixedVars), App(C, Seq(y, z, u) ++ fixedVars)),
                    App(C, Seq(x, z, u) ++ fixedVars)
                )
            )

            // all x,y: T, fixed...: Fixed... . ~C(x,x,y, fixed...)
            // for all x. x is not closer than itself to y
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)) ++ fixedArgVars, Not(App(C, Seq(x, x, y) ++ fixedVars)))
            
            // all x,y: T, fixed...: Fixed... . R*(x,y, fixed...) & ~(x=y) => C(x, s(x,y, fixed...), y, fixed...)
            // If distinct points x,y are in R*, then the next step from x to y (s(x,y)) is closer to y than x is
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    And(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), Not(Eq(x, y))),
                    App(C, Seq(x, App(s, Seq(x, y) ++ fixedVars), y) ++ fixedVars)
                )
            )

            // all x,y: T, fixed...: Fixed... . R*(x,y,fixed...) & ~(x=y) => R*(s(x,y, fixed...), y, fixed...)
            // if two distinct points x and y are in R*, then the next step from x to y (s(x,y)) is also in R* to y
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    And(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), Not(Eq(x, y))),
                    App(reflexiveClosureName, Seq(App(s, Seq(x, y) ++ fixedVars), y) ++ fixedVars)
                )
            )
            // Note this examples uses R as a relation, but funcContains can support R as a function
            // R is functionName,
            //all x,y: T, fixed...: Fixed... . R*(x,y, fixed...) & ~(x=y) => R(x, s(x,y, fixed...), fixed...)
            // for any two distinct points x,y in R*, the original R must connect x and its next value s(x,y)
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    And(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), Not(Eq(x, y))),
                    funcContains(functionName, x, App(s, Seq(x, y) ++ fixedVars), fixedVars)
                )
            )

            //all x,y,z: T, fixed...: Fixed... . R*(x,y,fixed...) & R*(y,z,fixed...) => R*(x,z,fixed...)
            // R* is transitive (over the closing arguments, not the fixed arguments) 
            closureAxioms += Forall(Seq(x,y,z).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    And(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), App(reflexiveClosureName, Seq(y, z) ++ fixedVars)),
                    App(reflexiveClosureName, Seq(x, z) ++ fixedVars)
                )
            )
            // all x,y: T, fixed...: Fixed... . R(x,y, fixed...) => R*(x,y, fixed...)
            // R* is a superset of R
            closureAxioms += Forall(Seq(x,y).map(_.of(sort)) ++ fixedArgVars,
                Implication(
                    funcContains(functionName, x, y, fixedVars),
                    App(reflexiveClosureName, Seq(x, y) ++ fixedVars)
                )
            )

            // all x: T, fixed...: Fixed... . R*(x, x, fixed...)
            // R* is reflexive
            closureAxioms += Forall(Seq(x.of(sort)) ++ fixedArgVars, App(reflexiveClosureName, Seq(x, x) ++ fixedVars))
        }

        def visitReflexiveClosure(rc: ReflexiveClosure): Term = {
            val reflexiveClosureName = getReflexiveClosureName(rc.functionName)
            // Find the sort we are closing over
            val sort = getClosingSortOfFunction(rc.functionName)

            // Define the reflexive closure if we have not defined it already
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

            // If the TC is not defined, define it
            if (!queryFunction(closureName)){
                // If the reflexive tc is not defined, define it
                if (!queryFunction(reflexiveClosureName)){
                    defineReflexiveClosure(sort, c.functionName)
                }

                val fixedSorts = getFixedSorts(c.functionName)
                val fixedVars = getFixedVars(fixedSorts.length)
                val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))
                // TC: TxTxFixed...->Bool
                closureFunctions += FuncDecl(closureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                val x = Var("x")
                val y = Var("y")
                val z = Var("z")
                // all x,y: T, fixed...: Fixed... . R^(x,y,fixed...) <=> exists z:T. R(x,z, fixed...) & R*(z,y, fixed...)
                // for any two points x,y. R^(x,y) iff there exists a single step R(x,z) where R*(z,y)
                // This avoids the reflection from R* by requiring R(x,z), then just uses the transitive part of R*
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
