package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.problemstate._
import fortress.util.Errors

import java.lang.IllegalArgumentException
import java.util.ArrayList
import scala.jdk.CollectionConverters._


class ClosureEliminatorEijck(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {
    // All closure functions we have generated (helps to avoid duplicates
    //val closureFunctions = scala.collection.mutable.Set[FuncDecl]()
    // Generated axioms
    //val closureAxioms = scala.collection.mutable.Set[Term]()
    override val visitor = new ClosureVisitorEijck

    // TODO fully understand how this is meant to be used
    /**
    * Perform the closure elimination and get the resulting term.
    * Don't forget to call getClosureFunctions() and getClosureAxioms()
    * after this.
    * Convert should only be called once per ClosureEliminator object.
    */
    /*
    Remove because we extend original now    
    def convert(): Term = {
        visitor.visit(topLevelTerm)
    }

    /** Returns the set of generated closure functions. Must be called after convert. */
    def getClosureFunctions: Set[FuncDecl] = closureFunctions.toSet
    
    /** Returns the set of generated skolem functions. Must be called after convert. */
    def getClosureAxioms: Set[Term] =  closureAxioms.toSet
    */

    class ClosureVisitorEijck extends ClosureVisitor {
        // TODO extend for other arguments. See getVarList in ClosureEliminator
        /** Axioms to define a midpoint being closer to the starting node than the ending node along a path for the given relation */
        def addClosenessAxioms(sort: Sort, functionName: String): String = {

            // How to actually ensure this does not exist from something else?
            val closenessName: String = "^Close^" + functionName;
            // If we already made this, then we can just leave.
            if (queryFunction(closenessName)){
                return closenessName;
            }

            val fixedSorts = getFixedSorts(functionName)
            val fixedVars = getFixedVars(fixedSorts.length)
            val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))

            val closenessArgs: List[Sort] = List(sort, sort, sort)

            auxilaryFunctions += FuncDecl.mkFuncDecl(closenessName, (Seq(sort, sort, sort) ++ fixedSorts).asJava, Sort.Bool)
            
            val x = Var(nameGen.freshName("x"))
            val y = Var(nameGen.freshName("y"))
            val z = Var(nameGen.freshName("z"))
            val u = Var(nameGen.freshName("u"))

            val axy = List(x.of(sort), y.of(sort))
            val axyz = List(x.of(sort), y.of(sort), z.of(sort))
            val au = u.of(sort)

            // Moved first to NNF
            closureAxioms += Forall((axyz :+ au) ++ fixedArgVars,
                Or(
                    Not(App(closenessName, List(x,y,u) ++ fixedVars)),
                    Not(App(closenessName, List(y,z,u) ++ fixedVars)),
                    App(closenessName, List(x,z,u) ++ fixedVars))
            )
            // No zero-distance
            closureAxioms += Forall(axy ++ fixedArgVars, Not(App(closenessName, List(x,x,y) ++ fixedVars)))
            // Single step NNF
            closureAxioms += Forall(axyz ++ fixedArgVars,
                Or(
                    Not(App(closenessName, List(x,y,y) ++ fixedVars)),
                    Not(App(closenessName, List(y,z,z) ++ fixedVars)),
                    Term.sortedEq(sort,x,z),
                    App(closenessName, List(x,z,z) ++ fixedVars)
                )
            )
            // idk but NNF
            closureAxioms += Forall(axyz ++ fixedArgVars,
                Or(
                    Not(App(closenessName, List(x,y,z) ++ fixedVars)),
                    Term.sortedEq(sort, y, z),
                    App(closenessName, List(y,z,z) ++ fixedVars)
                )
            )
            // Functions using the actual relation
            // NNF
            closureAxioms += Forall(axy ++ fixedArgVars,
                Or(
                    Not(funcContains(functionName, x, y, fixedVars)),
                    Term.sortedEq(sort, x,y),
                    App(closenessName, List(x,y,y) ++ fixedVars)
                )
            )
            // Closest unless something is closer NNF
            closureAxioms += Forall(axy ++ fixedArgVars,
                Or(
                    Not(App(closenessName, List(x,y,y) ++ fixedVars)),
                    Exists(z.of(sort),
                        And(
                            funcContains(functionName, x, z, fixedVars),
                            App(closenessName, List(x,z,y) ++ fixedVars)
                        )
                    )
                )
            )
            return closenessName;
        }

        
        // TODO support more arguments
        override def visitClosure(c: Closure): Term = {
            // Iff is allowed here it seems
            val functionName = c.functionName
            // idx is used for when there are more args
            val reflexiveClosureName = getReflexiveClosureName(functionName)
            val closureName = getClosureName(functionName)

            // Skip if we already did it
            if (!queryFunction(closureName)){
                // use index to find sort
                // Find the sort we are closing over
                val sort = getClosingSortOfFunction(functionName)

                val fixedSorts = getFixedSorts(functionName)
                val fixedVars = getFixedVars(fixedSorts.length)
                val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))
                
                // Declare the new function representing the closure
                closureFunctions += FuncDecl(closureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                
                // Set up variables (and their arguments) for axioms
                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val z = Var(nameGen.freshName("z"))
                val axy = List(x.of(sort), y.of(sort))
                val az = z.of(sort)

                // Generate the axioms to define closeness (checks if already done)
                val closenessName = this.addClosenessAxioms(sort, functionName)

                // define reflexive closure if we haven't already
                if(!queryFunction(reflexiveClosureName)){
                    // declare the function
                    closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, (Seq(sort, sort) ++ fixedSorts).asJava, Sort.Bool)
                    // Defined with closeness and one additional axiom
                    closureAxioms += Forall(axy ++ fixedArgVars,
                        Iff(
                            App(reflexiveClosureName, List(x,y) ++ fixedVars),
                            Or(
                                App(closenessName, List(x,y,y) ++ fixedVars),
                                Term.sortedEq(sort, x,y)
                            )
                        )
                    )
                }

                // Add an axiom to define how we use closeness to define closure
                closureAxioms += Forall(axy ++ fixedArgVars,
                    Iff(
                        App(closureName, List(x,y) ++ fixedVars),
                        Exists(az,
                            And(
                                funcContains(functionName, x, z, fixedVars),
                                Or(
                                    App(closenessName, List(z,y,y) ++ fixedVars),
                                    Term.sortedEq(sort, z,y)
                                )
                            )
                        )
                    )
                )

            }
            // println(closureFunctions)
            App(closureName, Seq(c.arg1, c.arg2) ++ c.fixedArgs).mapArguments(visit)
        }
        // TODO support more arguments
        override def visitReflexiveClosure(rc: ReflexiveClosure): Term = {
            // Iff is allowed here it seems
            val functionName = rc.functionName
            // idx is used for when there are more args
            val reflexiveClosureName = getReflexiveClosureName(functionName)
            val closureName = getClosureName(functionName)

            // Skip if we already did it
            if (!queryFunction(reflexiveClosureName)){
                // use index to find sort
                // Find the sort we are closing over
                val sort = getClosingSortOfFunction(functionName)

                val fixedSorts = getFixedSorts(functionName)
                val fixedVars = getFixedVars(fixedSorts.length)
                val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))

                // Declare reflexive closure
                closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, (Seq(sort, sort) ++ fixedSorts).asJava, Sort.Bool)
                
                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val axy = List(x.of(sort), y.of(sort))

                val closenessName = this.addClosenessAxioms(sort, functionName)
                
                closureAxioms += Forall(axy ++ fixedArgVars,
                    Iff(
                        App(reflexiveClosureName, List(x,y) ++ fixedVars),
                        Or(
                            App(closenessName, List(x,y,y) ++ fixedVars),
                            Term.sortedEq(sort, x,y)
                        )
                    )
                )
            }

            App(reflexiveClosureName, rc.allArguments).mapArguments(visit)
        }
        
    }
    
}