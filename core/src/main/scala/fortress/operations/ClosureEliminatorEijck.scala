package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.util.Errors
import java.lang.IllegalArgumentException
import java.util.ArrayList

import scala.jdk.CollectionConverters._


class ClosureEliminatorEijck(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Int], nameGen: NameGenerator) {
    // All closure functions we have generated (helps to avoid duplicates
    val closureFunctions = scala.collection.mutable.Set[FuncDecl]()
    // Generated axioms
    val closureAxioms = scala.collection.mutable.Set[Term]()
    val visitor = new ClosureVisitorEijck

    // TODO fully understand how this is meant to be used
    /**
    * Perform the closure elimination and get the resulting term.
    * Don't forget to call getClosureFunctions() and getClosureAxioms()
    * after this.
    * Convert should only be called once per ClosureEliminator object.
    */
    def convert(): Term = {
        visitor.visit(topLevelTerm)
    }

    /** Returns the set of generated closure functions. Must be called after convert. */
    def getClosureFunctions: Set[FuncDecl] = closureFunctions.toSet
    
    /** Returns the set of generated skolem functions. Must be called after convert. */
    def getClosureAxioms: Set[Term] =  closureAxioms.toSet


    class ClosureVisitorEijck extends TermVisitorWithTypeContext[Term](signature) {
        // Basically do nothing for each of the other terms
        override def visitTop: Term = Top
        
        override def visitBottom: Term = Bottom
        
        override def visitVar(variable: Var): Term = variable
        
        override def visitNot(term: Not): Term = term.mapBody(visit)
        
        override def visitAndList(term: AndList): Term = term.mapArguments(visit)
        
        override def visitOrList(term: OrList): Term = term.mapArguments(visit)
        
        override def visitDistinct(term: Distinct): Term = term.mapArguments(visit)
        
        override def visitIff(term: Iff): Term = term.mapArguments(visit)
        
        override def visitImplication(term: Implication): Term = term.mapArguments(visit)
        
        override def visitEq(term: Eq): Term = term.mapArguments(visit)
        
        override def visitApp(term: App): Term = term.mapArguments(visit)
        
        override def visitBuiltinApp(term: BuiltinApp): Term = term.mapArguments(visit)

        /** Check if a function has been defined */
        def queryFunction(name: String): Boolean = signature.hasFunctionWithName(name) || closureFunctions.exists(f => f.name == name)

        // TODO extend for other arguments. See getVarList in ClosureEliminator
        /** Axioms to define a midpoint being closer to the starting node than the ending node along a path for the given relation */
        def addClosenessAxioms(sort: Sort, functionName: String): String {
            // How to actually ensure this does not exist from something else?
            val closenessName: String = "^Close^" + functionName
            // If we already made this, then we can just leave.
            if (queryFunction(closenessName)){
                return closenessName;
            }

            val closenessArgs = new ArrayList(3)
            closenessArgs.add(sort)
            closenessArgs.add(sort)
            closenessArgs.add(sort)

            closureFunctions += FuncDecl.mkFuncDecl(closenessName, closenessArgs, Sort.Bool)
            
            val x = Var(nameGen.freshName("x"))
            val y = Var(nameGen.freshName("y"))
            val z = Var(nameGen.freshName("z"))
            val u = Var(nameGen.freshName("u"))

            val axy = List(x.of(sort), y.of(sort))
            val axyz = List(x.of(sort), y.of(sort), z.of(sort))
            val au = u.ofSort(sort)

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
            closenessAxioms += Forall(axyz,
                Or(
                    Not(App(closenessName, List(x,y,y))),
                    Not(App(closenessName, List(y,z,z))),
                    Eq(x,z),
                    App(closenessName, List(x,z,z))
                )
            )
            // idk but NNF
            closenessAxioms += Forall(axyz,
                Or(
                    Not(
                        App(closenessName, List(x,y,z)),
                        Eq(y,z),
                        App(closenessName, List(y,z,z))
                    )
                )
            )
            // Functions using the actual relation
            // NNF
            closenessAxioms += Forall(axy,
                Or(
                    Not(
                        App(functionName, List(x,y)),
                        Eq(x,y),
                        App(closenessName, List(x,y,y))
                    )
                )
            )
            // Closest unless something is closer NNF
            closenessAxioms += Forall(axy,
                Or(
                    Not(App(closenessName, List(x,y,y))),
                    Exists(z.ofSort(sort),
                        And(
                            App(functionName, List(x,z)),
                            App(closenessName, List(x,z,y))
                        )
                    )
                )
            )
            return closenessName;
        }

        
        // TODO support more arguments
        override def visitClosure(c: Closure){
            // Iff is allowed here it seems
            val functionName = rc.functionName
            // idx is used for when there are more args
            val idx = rc.arguments.indexOf(rc.arg1)
            val reflexiveClosureName = "*" + functionName
            val closureName = "^" + functionName

            // Skip if we already did it
            if (!queryFunction(closureName)){
                // use index to find sort
                val rel = signature.queryUninterpretedFunction(functionName).get
                var argSorts = new ArrayList(rel.argSorts.asJava)
                // TODO only use 0 instead of idx?
                val sort = argSorts.get(idx)

                // TODO should this be closureName
                // Declare reflexive closure
                closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, argSorts, Sort.Bool)
                
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
                    val rca = makeReflexiveClosureAxiom(reflexiveClosureName, closenessName)
                    closureAxioms += rca
                }

                // Add an axiom to define how we use closeness to define closure
                closureAxioms += Forall(axy,
                    Iff(
                        App(closureName, List(x,y)),
                        Exists(az,
                            And(
                                App(functionName, List(x,z)),
                                Or(
                                    App(closenessName, List(z,y,y)),
                                    Eq(z,y)
                                )
                            )
                        )
                    )
                )

            }
            App(closureName, c.arguments).mapArguments(visit)
        }
        // TODO support more arguments
        override def visitReflexiveClosure(rc: ReflexiveClosure){
            // Iff is allowed here it seems
            val functionName = rc.functionName
            // idx is used for when there are more args
            val idx = rc.arguments.indexOf(rc.arg1)
            val reflexiveClosureName = "*" + functionName
            val closureName = "^" + functionName

            // Skip if we already did it
            if (!queryFunction(reflexiveClosureName)){
                // use index to find sort
                val rel = signature.queryUninterpretedFunction(functionName).get
                var argSorts = new ArrayList(rel.argSorts.asJava)
                val sort = argSorts.get(idx)

                // Declare reflexive closure
                closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, argSorts, Sort.Bool)
                
                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val axy = List(x.of(sort), y.of(sort))

                val closenessName = this.addClosenessAxioms(sort, functionName)

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

            App(reflexiveClosureName, rc.arguments).mapArguments(visit)
        }

    }

    override def visitForallInner(term: Forall): Term = term.mapBody(visit)
        
    override def visitExistsInner(term: Exists): Term = term.mapBody(visit)
    
    override def visitDomainElement(d: DomainElement): Term = d
    
    override def visitIntegerLiteral(literal: IntegerLiteral): Term = literal
    
    override def visitBitVectorLiteral(literal: BitVectorLiteral): Term = literal
    
    override def visitEnumValue(e: EnumValue): Term = e

    override def visitIfThenElse(ite: IfThenElse): Term = IfThenElse(visit(ite.condition), visit(ite.ifTrue), visit(ite.ifFalse))


}