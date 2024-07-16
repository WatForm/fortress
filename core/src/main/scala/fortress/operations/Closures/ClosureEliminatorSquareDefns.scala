package fortress.operations

import fortress.data.NameGenerator
import fortress.msfol._
import fortress.problemstate._
import fortress.util.Errors

/** Removes closure given a term, which must be in negation normal form.
  * Free variables in the given term are ignored, so the top level term must be
  * closed with respect to the signature in question for this operation to be valid.
*/
class ClosureEliminatorSquareDefns(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {
    

    override val visitor = new ClosureVisitorSquare

    class ClosureVisitorSquare extends ClosureVisitor {
        // Finds the maximum number of squarings we need to do to form the closure
        def max_count(sort: Sort): Int = {
            val scope = scopes(sort)
            // ceil(log_2(scope)) + 1
            (math.ceil(math.log(scope.size) / math.log(2))).toInt + 1
        }
        // TODO support more arguments

        def expandClosure(functionName: String): Unit = {
            // Find the sort we are closing over
            val sort = getClosingSortOfFunction(functionName)
            Errors.Internal.precondition(scopes.contains(sort), "sort in closure must be bounded when using iterative eliminator.")
            // Record the sort as no longer being able change scope
            unchangingSorts += sort

            val closureName = getClosureName(functionName)

            
            // Set up for the new function representing the closure
            val fixedSorts = getFixedSorts(functionName)
            val fixedVars = getFixedVars(fixedSorts.length)
            val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))

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
                auxilaryDefns += FunctionDefinition(iterationName, axy ++ fixedArgVars, Sort.Bool, Or(
                    // At least the previous
                    funcContains(previousRelation, x, y, fixedVars),
                    // One more step
                    Exists(az,
                        And(
                            funcContains(previousRelation, x, z, fixedVars),
                            funcContains(previousRelation, z, y, fixedVars)
                        )
                    )
                ))
                previousRelation = iterationName
            }
            // Define the closure itself
            closureDefns += FunctionDefinition(closureName, axy ++ fixedArgVars, Sort.Bool, Or(
                // At least the previous
                funcContains(previousRelation, x, y, fixedVars),
                // One more step
                Exists(az,
                    And(
                        funcContains(previousRelation, x, z, fixedVars),
                        funcContains(previousRelation, z, y, fixedVars)
                    )
                )
            ))
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
            App(closureName, c.allArguments).mapArguments(visit)
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
                // Find the sort we are closing over
                val sort = getClosingSortOfFunction(functionName)
                // Record the sort as no longer being able change scope
                unchangingSorts += sort

                val fixedSorts = getFixedSorts(functionName)
                val fixedVars = getFixedVars(fixedSorts.length)
                val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))

                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val axy = List(x.of(sort), y.of(sort))

                closureDefns += FunctionDefinition(reflexiveClosureName, axy ++ fixedArgVars, Sort.Bool, Or(
                    App(closureName, Seq(x, y) ++ fixedVars),
                    Eq(x, y),
                ))
            }

            App(reflexiveClosureName, rc.allArguments).mapArguments(visit)
        }
    }
}