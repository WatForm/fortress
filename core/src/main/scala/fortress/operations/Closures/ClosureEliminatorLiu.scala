package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.problemstate._

import java.util.ArrayList
import scala.jdk.CollectionConverters._


class ClosureEliminatorLiu(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {

    override val visitor = new ClosureVisitorLiu

    class ClosureVisitorLiu extends ClosureVisitor {

        def nameAuxFunction(closedName: String): String = "^LiuEtAlP" + closedName

        def defineAuxFunction(sort: Sort, functionName: String): Unit = {
            val closureName = getClosureName(functionName)
            val p = nameAuxFunction(closureName)

            val fixedSorts = getFixedSorts(functionName)
            val fixedVars = getFixedVars(fixedSorts.length)
            val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))

            // p:TxTxfixedSorts->Int represents distance on shortest path
            auxilaryFunctions += FuncDecl(p, Seq(sort, sort) ++ fixedSorts, Sort.Int)

            val x = Var(nameGen.freshName("x"))
            val y = Var(nameGen.freshName("y"))
            val z = Var(nameGen.freshName("z"))
            val axy = List(x.of(sort), y.of(sort))
            val axyz = List(x.of(sort), y.of(sort), z.of(sort))
            val az = z.of(sort)
            
            // all x,y:T, fixed...:Fixed... . R(x,y,fixed...) <=> p(x,y,fixed...) = 1
            // If there is an edge from x to y on the original R, then the shortest path is length 1
            closureAxioms += Forall(axy ++ fixedArgVars,
                Iff(
                    funcContains(functionName, x, y, fixedVars),
                    Term.mkEq(App(p, Seq(x,y) ++ fixedVars), IntegerLiteral(1))
                )
            )

            // If p(x,y, fixed...) > 0 then there exists a path from x to y
            // if there is a path from x to y and y to z then there exists a path from x to z
            closureAxioms += Forall(axyz ++ fixedArgVars,
                Implication(
                    And(
                        Term.mkGT(App(p, Seq(x,y) ++ fixedVars), IntegerLiteral(0)),
                        Term.mkGT(App(p, Seq(y,z) ++ fixedVars), IntegerLiteral(0)),
                    ),
                    Term.mkGT(App(p, Seq(x,z) ++ fixedVars), IntegerLiteral(0))
                )
            )

            // Take a step
            // all x,y:T, fixed...:Fixed... . p(x,y,fixed...) > 1 => exists z: T. p(x,z, fixed...) = 1 & p(x,y,fixed...) = p(z, y, fixed...) + 1.
            // If there is a path of length > 1 from x to y then there exists a point z st there is an edge from x to z and
            //   the shortest path from x to y has a length equal to 1 plus the shortest length from z to y.
            closureAxioms += Forall(axy ++ fixedArgVars,
                Implication(
                    Term.mkGT(App(p, Seq(x,y) ++ fixedVars), IntegerLiteral(1)),
                    Exists(az,
                        And(
                            Term.mkEq(App(p, Seq(x,z) ++ fixedVars), IntegerLiteral(1)),
                            Term.mkEq(
                                App(p, Seq(x,y) ++ fixedVars),
                                Term.mkPlus(App(p, Seq(z,y) ++ fixedVars), IntegerLiteral(1))
                            )
                        )
                    )
                )
            )
        }
        override def visitReflexiveClosure(rc: ReflexiveClosure): Term = {
            val functionName = rc.functionName
            // idx is used for when there are more args
            val reflexiveClosureName = getReflexiveClosureName(functionName)
            val closureName = getClosureName(functionName)

            // If we have yet to define R*, do so now
            if (!queryFunction(reflexiveClosureName)){
                // Build the closure
                // Find the sort we are closing over
                val sort = getClosingSortOfFunction(functionName)

                // If we haven't defined p, do so now
                val p = nameAuxFunction(closureName)
                if(!queryFunction(p)){
                    defineAuxFunction(sort, functionName)
                }

                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val axy = List(x.of(sort), y.of(sort))

                val fixedSorts = getFixedSorts(functionName)
                val fixedVars = getFixedVars(fixedSorts.length)
                val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))


                // x,y is in TC iff x=y or there is a path from x to y (p(x,y) > 0)
                closureFunctions += FuncDecl(reflexiveClosureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                closureAxioms += Forall(axy ++ fixedArgVars,
                    Iff(
                        App(reflexiveClosureName, Seq(x,y) ++ fixedVars),
                        Or(
                            Term.mkGT(App(p, Seq(x,y) ++ fixedVars), IntegerLiteral(0)),
                            Eq(x,y)
                        )
                    )
                )
            }

            App(reflexiveClosureName, Seq(rc.arg1, rc.arg2) ++ rc.fixedArgs).mapArguments(visit)
        }

        override def visitClosure(c: Closure): Term = {
            val functionName = c.functionName
            // idx is used for when there are more args
            val reflexiveClosureName = getReflexiveClosureName(functionName)
            val closureName = getClosureName(functionName)


            // If R^ is undefined, define it now
            if (!queryFunction(closureName)){
                // Build the closure
                // Find the sort we are closing over
                val sort = getClosingSortOfFunction(functionName)

                // define p if it has not yet been defined
                val p = nameAuxFunction(closureName)
                if(!queryFunction(p)){
                    defineAuxFunction(sort, functionName)
                }

                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val axy = List(x.of(sort), y.of(sort))

                val fixedSorts = getFixedSorts(functionName)
                val fixedVars = getFixedVars(fixedSorts.length)
                val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))

                // Closure when P > 0
                // R^(x,y) iff p(x,y) > 0
                // If there is a path of length > 0 between two points, then those points are in the transitive closure
                closureFunctions += FuncDecl(closureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                closureAxioms += Forall(axy ++ fixedArgVars,
                    Iff(
                        App(closureName, Seq(x,y) ++ fixedVars),
                        Term.mkGT(App(p, Seq(x,y) ++ fixedVars), IntegerLiteral(0))
                    )
                )
            }

            App(closureName, Seq(c.arg1, c.arg2) ++ c.fixedArgs).mapArguments(visit)
        }

    }
}