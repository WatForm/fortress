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


            // C: TxTxTxFixed... -> Bool
            auxilaryFunctions += FuncDecl.mkFuncDecl(closenessName, (Seq(sort, sort, sort) ++ fixedSorts).asJava, Sort.Bool)
            
            val x = Var(nameGen.freshName("x"))
            val y = Var(nameGen.freshName("y"))
            val z = Var(nameGen.freshName("z"))
            val u = Var(nameGen.freshName("u"))

            val axy = List(x.of(sort), y.of(sort))
            val axyz = List(x.of(sort), y.of(sort), z.of(sort))
            val au = u.of(sort)

            // For these comments we will use C for the closeness relation.
            // We want to define C such that C(a,x,z) is true iff x is closer to z than a is 
            // along the shortest path from a to z

            // Moved first to NNF
            // forall a,x,y,z,u: T, fixed...:Fixed... . ~C(x,y,u, fixed...) | ~C(y,z,u,fixed...) | C(x,z,u, fixed...)
            // ALT: forall a,x,y,z,u: T, fixed...:Fixed... . C(x,y,u, fixed...) & C(y,z,u,fixed...) => C(x,z,u, fixed...)

            // If y is along the shortest path from x to u (and not x), and z is along the shortest path from y to u (and not y)
            // then, z is along the shortest path from x to u (and not x)
            closureAxioms += Forall((axyz :+ au) ++ fixedArgVars,
                Or(
                    Not(App(closenessName, List(x,y,u) ++ fixedVars)),
                    Not(App(closenessName, List(y,z,u) ++ fixedVars)),
                    App(closenessName, List(x,z,u) ++ fixedVars))
            )

            // all x,y:T,fixed...:Fixed... . ~C(x,x,y,fixed...)
            // No point is closer than itself along the shortest path to any point
            closureAxioms += Forall(axy ++ fixedArgVars, Not(App(closenessName, List(x,x,y) ++ fixedVars)))


            // Single step NNF
            // Note that C(a,b,b) essentially means that there is a path from a to B in R as b will always be closer
            // to iself than a if a path between them exists.
            //all x,y,z:T,fixed...:Fixed... . ~C(x,y,y,fixed...) | ~C(y,z,z,fixed...) | x=z | C(x,z,z,fixed...)
            // ALT: all x,y,z:T,fixed...:Fixed... . C(x,y,y,fixed...) & C(y,z,z,fixed...) & ~(x=z) => C(x,z,z,fixed...)
            // If a path from x to y exists, and a path from y to z exists, then a path from x to z exists, BUT
            // Do not include that if x and z are the same, because a point cannot be closer than itself to anything
            closureAxioms += Forall(axyz ++ fixedArgVars,
                Or(
                    Not(App(closenessName, List(x,y,y) ++ fixedVars)),
                    Not(App(closenessName, List(y,z,z) ++ fixedVars)),
                    Eq(x,z),
                    App(closenessName, List(x,z,z) ++ fixedVars)
                )
            )

            // idk but NNF
            // all x,y,z:T,fixed...:Fixed... . ~(C(x,y,z,fixed...)) | y=z | C(y,z,z,fixed...)
            // ALT: all x,y,z:T,fixed...:Fixed... . C(x,y,z,fixed...) & ~(y=z) => C(y,z,z, fixed...)
            // If y is along the path from x to z, but not z itself, then there is a path from y to z.
            closureAxioms += Forall(axyz ++ fixedArgVars,
                Or(
                    Not(App(closenessName, List(x,y,z) ++ fixedVars)),
                    Eq(y, z),
                    App(closenessName, List(y,z,z) ++ fixedVars)
                )
            )

            // all x,y:T,fixed...:Fixed... . ~R(x,y,fixed...) | x=y => C(x,y,y,fixed...)
            // ALT: all x,y:T,fixed...:Fixed... . R(x,y,fixed...) & ~(x=y) => C(x,y,y,fixed...)
            // If there is an edge from x to y in R and x !=y, then y is closer to itself than x.
            // ALT: If there is an edge from x to y in R and x != y then there is a path from x to y.
            // This is part of the statement C(a,b,b) means there is a path from a to b.
            closureAxioms += Forall(axy ++ fixedArgVars,
                Or(
                    Not(funcContains(functionName, x, y, fixedVars)),
                    Eq(x,y),
                    App(closenessName, List(x,y,y) ++ fixedVars)
                )
            )
            // all x,y:T,fixed...:Fixed... . ~C(x,y,y,fixed...) | exists z:T. R(x,z,fixed...) & C(x,z,y, fixed...)
            // ALT: all x,y:T,fixed...:Fixed... . C(x,y,y, fixed...) => exists z:T. R(x,z,fixed...) & C(x,z,y, fixed...)
            // If there is a path from x to y (that is not just x back to itself), then there is an edge from x to z
            //    and z is along the shortest path from x to y. 
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

        
        
        override def visitClosure(c: Closure): Term = {
            // Iff is allowed here it seems
            val functionName = c.functionName
            // idx is used for when there are more args
            val reflexiveClosureName = getReflexiveClosureName(functionName)
            val closureName = getClosureName(functionName)

            // If we have not defined the closure, define it.
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
                    // declare the function R*: TxTxFixed...->Bool
                    closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, (Seq(sort, sort) ++ fixedSorts).asJava, Sort.Bool)
                    // Defined with closeness and one additional axiom
                    // all x,y:T,fixed...:Fixed... . R*(x,y,fixed...) <=> C(x,y,y,fixed...) | x=y
                    // For any two points, they are in the reflexive closure iff 
                    // (they are distinct and) there is a path between them OR they are the same point
                    // If you change this, be sure to change it for reflexive tc as well
                    closureAxioms += Forall(axy ++ fixedArgVars,
                        Iff(
                            App(reflexiveClosureName, List(x,y) ++ fixedVars),
                            Or(
                                App(closenessName, List(x,y,y) ++ fixedVars),
                                Eq(x,y)
                            )
                        )
                    )
                }

                // Define the normal transitive closure in terms of the reflexive
                // You must take a step to ensure its not just the added every point is related to itself
                // all x,y:T,fixed...:Fixed... . R^(x,y,fixed...) <=> exists z: T. R(x,z) & (C(z,y,y,fixed...), z=y)
                // For any two points x,y they are in R^ iff there is an edge from x to some z in the original R such that
                //   there is a path from z to y (and z != y) OR z = y
                closureAxioms += Forall(axy ++ fixedArgVars,
                    Iff(
                        App(closureName, List(x,y) ++ fixedVars),
                        Exists(az,
                            And(
                                funcContains(functionName, x, z, fixedVars),
                                Or(
                                    App(closenessName, List(z,y,y) ++ fixedVars),
                                    Eq(z,y)
                                )
                            )
                        )
                    )
                )

            }
            
            App(closureName, Seq(c.arg1, c.arg2) ++ c.fixedArgs).mapArguments(visit)
        }

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


                // Defined with closeness and one additional axiom
                // all x,y:T,fixed...:Fixed... . R*(x,y,fixed...) <=> C(x,y,y,fixed...) | x=y
                // For any two points, they are in the reflexive closure iff 
                // (they are distinct and) there is a path between them OR they are the same point
                // If you change this, be sure to change it for normal tc as well
                closureAxioms += Forall(axy ++ fixedArgVars,
                    Iff(
                        App(reflexiveClosureName, List(x,y) ++ fixedVars),
                        Or(
                            App(closenessName, List(x,y,y) ++ fixedVars),
                            Eq(x,y)
                        )
                    )
                )
            }

            App(reflexiveClosureName, rc.allArguments).mapArguments(visit)
        }
        
    }
    
}