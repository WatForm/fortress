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

            auxilaryFunctions += FuncDecl(p, Seq(sort, sort) ++ fixedSorts, Sort.Int)

            val x = Var(nameGen.freshName("x"))
            val y = Var(nameGen.freshName("y"))
            val z = Var(nameGen.freshName("z"))
            val axy = List(x.of(sort), y.of(sort))
            val axyz = List(x.of(sort), y.of(sort), z.of(sort))
            val az = z.of(sort)
            
            // It takes 1 step in original function
            closureAxioms += Forall(axy ++ fixedArgVars,
                Iff(
                    funcContains(functionName, x, y, fixedVars),
                    Term.mkEq(App(p, Seq(x,y) ++ fixedVars), IntegerLiteral(1))
                )
            )
            // P remains positive
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

            if (!queryFunction(reflexiveClosureName)){
                // Build the closure
                val rel = signature.queryFunctionDeclaration(functionName).get
                val sort = rel.argSorts(0)

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


                // Reflexive Closure when P > 0 or x = y
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

            if (!queryFunction(closureName)){
                // Build the closure
                val rel = signature.queryFunctionDeclaration(functionName).get
                var argSorts = new ArrayList(rel.argSorts.asJava)
                val sort = rel.argSorts(0)

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