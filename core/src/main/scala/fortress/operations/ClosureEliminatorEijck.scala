package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.util.Errors
import java.lang.IllegalArgumentException
import java.util.ArrayList

import scala.jdk.CollectionConverters._


class ClosureEliminatorEijck(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Int], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {
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
        def addClosenessAxioms(sort: Sort, functionName: String, fixedArgs: Seq[Term]): String = {
            // How to actually ensure this does not exist from something else?
            val closenessName: String = "^Close^" + functionName;
            // If we already made this, then we can just leave.
            if (queryFunction(closenessName)){
                return closenessName;
            }

            val closenessArgs: List[Sort] = List(sort, sort, sort)

            closureFunctions += FuncDecl.mkFuncDecl(closenessName, sort, sort, sort, Sort.Bool)
            
            val x = Var(nameGen.freshName("x"))
            val y = Var(nameGen.freshName("y"))
            val z = Var(nameGen.freshName("z"))
            val u = Var(nameGen.freshName("u"))

            val axy = List(x.of(sort), y.of(sort))
            val axyz = List(x.of(sort), y.of(sort), z.of(sort))
            val au = u.of(sort)

            // Moved first to NNF
            closureAxioms += Forall(axyz :+ au,
                Or(
                    Not(App(closenessName, List(x,y,u))),
                    Not(App(closenessName, List(y,z,u))),
                    App(closenessName, List(x,z,u)))
            )
            // No zero-distance
            closureAxioms += Forall(axy, Not(App(closenessName, List(x,x,y))))
            // Single step NNF
            closureAxioms += Forall(axyz,
                Or(
                    Not(App(closenessName, List(x,y,y))),
                    Not(App(closenessName, List(y,z,z))),
                    Eq(x,z),
                    App(closenessName, List(x,z,z))
                )
            )
            // idk but NNF
            closureAxioms += Forall(axyz,
                Or(
                    Not(App(closenessName, List(x,y,z))),
                    Eq(y, z),
                    App(closenessName, List(y,z,z))
                )
            )
            // Functions using the actual relation
            // NNF
            closureAxioms += Forall(axy,
                Or(
                    Not(funcContains(functionName, x, y, fixedArgs)),
                    Eq(x,y),
                    App(closenessName, List(x,y,y))
                )
            )
            // Closest unless something is closer NNF
            closureAxioms += Forall(axy,
                Or(
                    Not(App(closenessName, List(x,y,y))),
                    Exists(z.of(sort),
                        And(
                            funcContains(functionName, x, z, fixedArgs),
                            App(closenessName, List(x,z,y))
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
                val rel = signature.queryUninterpretedFunction(functionName).get
                val sort = rel.argSorts(0)

                // Declare the new function representing the closure
                closureFunctions += FuncDecl.mkFuncDecl(closureName, sort, sort, Sort.Bool)
                
                // Set up variables (and their arguments) for axioms
                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val z = Var(nameGen.freshName("z"))
                val axy = List(x.of(sort), y.of(sort))
                val az = z.of(sort)

                // Generate the axioms to define closeness (checks if already done)
                val closenessName = this.addClosenessAxioms(sort, functionName, c.fixedArgs)

                // define reflexive closure if we haven't already
                if(!queryFunction(reflexiveClosureName)){
                    // declare the function
                    closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, sort, sort, Sort.Bool)
                    // Defined with closeness and one additional axiom
                    closureAxioms += Forall(axy,
                        Iff(
                            App(reflexiveClosureName, List(x,y)),
                            Or(
                                App(closenessName, List(x,y,y)),
                                Eq(x,y)
                            )
                        )
                    )
                }

                // Add an axiom to define how we use closeness to define closure
                closureAxioms += Forall(axy,
                    Iff(
                        App(closureName, List(x,y)),
                        Exists(az,
                            And(
                                funcContains(functionName, x, z, c.fixedArgs),
                                Or(
                                    App(closenessName, List(z,y,y)),
                                    Eq(z,y)
                                )
                            )
                        )
                    )
                )

            }
            App(closureName, Seq(c.arg1, c.arg2)).mapArguments(visit)
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
                val rel = signature.queryUninterpretedFunction(functionName).get
                var argSorts = new ArrayList(rel.argSorts.asJava)
                val sort = rel.argSorts(0)

                // Declare reflexive closure
                closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, sort, sort, Sort.Bool)
                
                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val axy = List(x.of(sort), y.of(sort))

                val closenessName = this.addClosenessAxioms(sort, functionName, rc.fixedArgs)
                
                closureAxioms += Forall(axy,
                    Iff(
                        App(reflexiveClosureName, List(x,y)),
                        Or(
                            App(closenessName, List(x,y,y)),
                            Eq(x,y)
                        )
                    )
                )
            }

            App(reflexiveClosureName, Seq(rc.arg1, rc.arg2)).mapArguments(visit)
        }
        
    }
    
}