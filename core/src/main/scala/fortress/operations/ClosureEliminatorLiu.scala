package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import java.util.ArrayList

import scala.jdk.CollectionConverters._


class ClosureEliminatorLiu(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {

    override val visitor = new ClosureVisitorLiu

    class ClosureVisitorLiu extends ClosureVisitor {

        def nameAuxFunction(closedName: String): String = "^LiuEtAlP" + closedName

        def defineAuxFunction(sort: Sort, functionName: String): Unit = {
            val closureName = getClosureName(functionName)
            val p = nameAuxFunction(closureName)

            closureFunctions += FuncDecl.mkFuncDecl(p, sort, sort, Sort.Int)

            val x = Var(nameGen.freshName("x"))
            val y = Var(nameGen.freshName("y"))
            val z = Var(nameGen.freshName("z"))
            val axy = List(x.of(sort), y.of(sort))
            val axyz = List(x.of(sort), y.of(sort), z.of(sort))
            val az = z.of(sort)
            
            // It takes 1 step in original function
            closureAxioms += Forall(axy,
                Iff(
                    funcContains(functionName, x, y),
                    Term.mkEq(App(p,x,y), IntegerLiteral(1))
                )
            )
            // P remains positive
            closureAxioms += Forall(axyz,
                Implication(
                    And(
                        Term.mkGT(App(p,x,y), IntegerLiteral(0)),
                        Term.mkGT(App(p,y,z), IntegerLiteral(0)),
                    ),
                    Term.mkGT(App(p,x,z), IntegerLiteral(0))
                )
            )

            // Take a step
            closureAxioms += Forall(axy,
                Implication(
                    Term.mkGT(App(p,x,y), IntegerLiteral(1)),
                    Exists(az,
                        And(
                            Term.mkEq(App(p,x,z), IntegerLiteral(1)),
                            Term.mkEq(
                                App(p,x,y),
                                Term.mkPlus(App(p,z,y), IntegerLiteral(1))
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
                val rel = signature.queryUninterpretedFunction(functionName).get
                val sort = rel.argSorts(0)

                val p = nameAuxFunction(closureName)
                if(!queryFunction(p)){
                    defineAuxFunction(sort, functionName)
                }

                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val axy = List(x.of(sort), y.of(sort))


                // Reflexive Closure when P > 0 or x = y
                closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, sort, sort, Sort.Bool)
                closureAxioms += Forall(axy,
                    Iff(
                        App(reflexiveClosureName,x,y),
                        Or(
                            Term.mkGT(App(p,x,y), IntegerLiteral(0)),
                            Eq(x,y)
                        )
                    )
                )
            }

            App(reflexiveClosureName, Seq(rc.arg1, rc.arg2)).mapArguments(visit)
        }

        override def visitClosure(c: Closure): Term = {
            val functionName = c.functionName
            // idx is used for when there are more args
            val reflexiveClosureName = getReflexiveClosureName(functionName)
            val closureName = getClosureName(functionName)

            if (!queryFunction(closureName)){
                // Build the closure
                val rel = signature.queryUninterpretedFunction(functionName).get
                var argSorts = new ArrayList(rel.argSorts.asJava)
                val sort = rel.argSorts(0)

                val p = nameAuxFunction(closureName)
                if(!queryFunction(p)){
                    defineAuxFunction(sort, functionName)
                }

                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val axy = List(x.of(sort), y.of(sort))
                // Closure when P > 0
                closureFunctions += FuncDecl.mkFuncDecl(closureName, sort, sort, Sort.Bool)
                closureAxioms += Forall(axy,
                    Iff(
                        App(closureName,x,y),
                        Term.mkGT(App(p,x,y), IntegerLiteral(0))
                    )
                )
            }

            App(closureName, Seq(c.arg1, c.arg2)).mapArguments(visit)
        }

    }
}