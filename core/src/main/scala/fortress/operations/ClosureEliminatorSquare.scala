package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.util.Errors
import java.lang.IllegalArgumentException
import java.util.ArrayList

import scala.jdk.CollectionConverters._

/** Removes closure given a term, which must be in negation normal form.
  * Free variables in the given term are ignored, so the top level term must be
  * closed with respect to the signature in question for this operation to be valid.
*/
class ClosureEliminatorSquare(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Int], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {
    

    override val visitor = new ClosureVisitorSquare

    class ClosureVisitorSquare extends ClosureVisitor {
        // Finds the maximum number of squarings we need to do to form the closure
        def max_count(sort: Sort): Int = {
            val scope = scopes(sort)
            // ceil(log_2(scope)) + 1
            (math.ceil(math.log(scope) / math.log(2))).toInt + 1
        }
        // TODO support more arguments

        def expandClosure(functionName: String): Unit = {
            val rel = signature.functionWithName(functionName).get
            val sort: Sort = rel.argSorts(0)

            val closureName = "^" + functionName
            
            // Declare the new function representing the closure
            closureFunctions += FuncDecl.mkFuncDecl(closureName, sort, sort, Sort.Bool)

            // Set up variables (and their arguments) for axioms
            val x = Var(nameGen.freshName("x"))
            val y = Var(nameGen.freshName("y"))
            val z = Var(nameGen.freshName("z")) 
            val axy = List(x.of(sort), y.of(sort))
            val az = z.of(sort)

            
            var previousRelation = functionName
            

            // iteratively square the relation
            for (iter <- 1 to max_count(sort)){
                // Make the next squared level
                val iterationName = functionName + "^" + iter.toString()
                val iterationDecl = FuncDecl.mkFuncDecl(iterationName, sort, sort, Sort.Bool)
                closureFunctions += iterationDecl
                // Define it
                closureAxioms += Forall(axy,
                    Iff(App(iterationName, x, y),
                        Or(
                            // At least the previous
                            funcContains(previousRelation, x, y),
                            // One more step
                            Exists(az,
                                And(
                                    funcContains(previousRelation, x, z),
                                    funcContains(previousRelation, z, y)
                                )
                            )
                        )
                    )
                )

                previousRelation = iterationName
            }
            // Define the closure itself
            closureAxioms += Forall(axy,
                    Iff(App(closureName, x, y),
                        Or(
                            // At least the previous
                            funcContains(previousRelation, x, y),
                            // One more step
                            Exists(az,
                                And(
                                    funcContains(previousRelation, x, z),
                                    funcContains(previousRelation, z, y)
                                )
                            )
                        )
                    )
                )
        }
        override def visitClosure(c: Closure): Term = {
             // Iff is allowed here it seems
            val functionName = c.functionName
            val reflexiveClosureName = "*" + functionName
            val closureName = "^" + functionName

            if (!queryFunction(closureName)){
                // Closure has not been expanded. Do so now!
                expandClosure(functionName)
            }
            App(closureName, c.arguments).mapArguments(visit)
        }
        // TODO support more arguments
        override def visitReflexiveClosure(rc: ReflexiveClosure): Term = {
            // Iff is allowed here it seems
            val functionName = rc.functionName
            val reflexiveClosureName = "*" + functionName
            val closureName = "^" + functionName

            // Skip if we already did it
            if (!queryFunction(reflexiveClosureName)){
                if (!queryFunction(closureName)) {
                    expandClosure(functionName)
                }
                val rel = signature.functionWithName(functionName).get
                val sort = rel.argSorts(0)
                closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, sort, sort, Sort.Bool)
                
                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val axy = List(x.of(sort), y.of(sort))
                closureAxioms += Forall(axy,
                    Iff(App(reflexiveClosureName, x, y),
                        Or(
                            App(closureName, x, y),
                            Eq(x,y)
                        )

                    )
                )
            }

            App(reflexiveClosureName, rc.arguments).mapArguments(visit)
        }
    }
}