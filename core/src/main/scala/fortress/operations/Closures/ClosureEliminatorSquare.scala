package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.problemstate._
import fortress.util.Errors

import java.lang.IllegalArgumentException
import java.util.ArrayList
import scala.jdk.CollectionConverters._

/** Removes closure given a term, which must be in negation normal form.
  * Free variables in the given term are ignored, so the top level term must be
  * closed with respect to the signature in question for this operation to be valid.
*/
class ClosureEliminatorSquare(private val useDefns: Boolean = true, topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {

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

            // Declare the new function representing the closure
            val fixedSorts = getFixedSorts(functionName)
            val fixedVars = getFixedVars(fixedSorts.length)
            val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))
            if (!useDefns) {
                closureFunctions += FuncDecl(closureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
            }

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
                val body = Or(
                    // At least the previous
                    funcContains(previousRelation, x, y, fixedVars),
                    // One more step
                    Exists(az,
                        And(
                            funcContains(previousRelation, x, z, fixedVars),
                            funcContains(previousRelation, z, y, fixedVars)
                        )
                    )
                )
                if (useDefns) {
                    auxilaryDefns += FunctionDefinition(iterationName, axy ++ fixedArgVars, Sort.Bool, body)
                } else {
                    val iterationDecl = FuncDecl(iterationName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                    auxilaryFunctions += iterationDecl
                    // Define it
                    closureAxioms += Forall(axy ++ fixedArgVars, Iff(App(iterationName, Seq(x, y) ++ fixedVars), body))
                }

                previousRelation = iterationName
            }
            // Define the closure itself
            val body = Or(
                // At least the previous
                funcContains(previousRelation, x, y, fixedVars),
                // One more step
                Exists(az,
                    And(
                        funcContains(previousRelation, x, z, fixedVars),
                        funcContains(previousRelation, z, y, fixedVars)
                    )
                )
            )
            if (useDefns) {
                closureDefns += FunctionDefinition(closureName, axy ++ fixedArgVars, Sort.Bool, body)
            } else {
                closureAxioms += Forall(axy ++ fixedArgVars, Iff(App(closureName, Seq(x, y) ++ fixedVars), body))
            }
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

                if (!useDefns) {
                    closureFunctions += FuncDecl(reflexiveClosureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                }

                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val axy = List(x.of(sort), y.of(sort))

                val body = Or(
                    App(closureName, Seq(x, y) ++ fixedVars),
                    Eq(x, y),
                )
                if (useDefns) {
                    closureDefns += FunctionDefinition(reflexiveClosureName, axy ++ fixedArgVars, Sort.Bool, body)
                } else {
                    closureAxioms += Forall(axy ++ fixedArgVars, Iff(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), body))
                }
            }

            App(reflexiveClosureName, rc.allArguments).mapArguments(visit)
        }
    }
}