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

class ClosureEliminatorIterative(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {


    override val visitor: ClosureVisitor = new ClosureVisitorIterative
    
    class ClosureVisitorIterative extends ClosureVisitor {
        /** Check if a function has been defined */

        override def visitClosure(c: Closure): Term = {
            // The name of the function we are generating the closure for
            var functionName = c.functionName
            // The name that this closure will have (idx specific)
            val closureName = getClosureName(functionName)
            val reflexiveClosureName = getReflexiveClosureName(functionName)

            // Function that checks if the function already exists or we have generated it
            def queryFunction(name: String): Boolean = signature.hasFuncDeclWithName(name) || closureFunctions.exists(f => f.name == name)

            // If we have not generated the function yet
            if (!queryFunction(closureName)) {
                // Look at original function to make declaration for the closure function
                // Find the sort we are closing over
                val sort = getClosingSortOfFunction(functionName)
                Errors.Internal.precondition(scopes.contains(sort), "sort in closure must be bounded when using iterative eliminator.")
                // Record the sort as no longer being able change scope
                unchangingSorts += sort

                val fixedSorts = getFixedSorts(functionName)
                val fixedVars = getFixedVars(fixedSorts.length)
                val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))
                closureFunctions += FuncDecl(closureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                val x = Var(nameGen.freshName("x"));
                val y = Var(nameGen.freshName("y"));

                val avars = List(x.of(sort), y.of(sort))
                val z = Var(nameGen.freshName("z"))
                val az = z.of(sort)
                val scope = scopes(sort)
                // ?? Is this just replacing the two we are checkign with ex R(a,b,c,x,y) we can close on xy?
                // Why do we assume they are adjacent? Partial application?
//                def getVarList(v1: Var, v2: Var): List[Var] = (vars.slice(0, idx) :+ v1 :+ v2) ::: vars.slice(idx+2, vars.size)
                if ( scope.size < 100) {
                    // Using the technique of repeated squaring
                    for (s <- 1 until scala.math.ceil(scala.math.log(scope.size)/scala.math.log(2)).toInt) {
                        // Make a new function with a similar name
                        val newFunctionName = nameGen.freshName(functionName);
                        // It uses the same arguments
                        auxilaryFunctions += FuncDecl(newFunctionName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                        // For every input,
                        closureAxioms += Forall(avars ++ fixedArgVars, Iff(App(newFunctionName, Seq(x, y) ++ fixedVars), // For every inputs R_n+1(x,y) <=>
                            Or( // 1 of 2 things
                                funcContains(functionName, x, y, fixedVars), // R_n(x,y) already existed in the original
                                Exists(az, // There is some z where R_n(x,z) and R_n(z,y)
                                    And(
                                        funcContains(functionName, x, z, fixedVars), 
                                        funcContains(functionName, z, y, fixedVars)
                                    )   
                                ))))
                        functionName = newFunctionName;
                    }
                    closureAxioms += Forall(avars ++ fixedArgVars, Iff(App(closureName, Seq(x, y) ++ fixedVars), Or(funcContains(functionName, x, y, fixedVars), Exists(az, And(funcContains(functionName, x, z, fixedVars), funcContains(functionName, z, y, fixedVars))))))
                } else if (queryFunction(reflexiveClosureName)) {
                    // If we have the reflexive closure, just use that
                    // Reflexive closure R(x,y) <=> exists z: R(x,z) and R(z,y)
                    closureAxioms += Forall(avars ++ fixedArgVars,
                        Iff(App(closureName, Seq(x, y) ++ fixedVars), Exists(az, And(funcContains(functionName, x, z, fixedVars), App(reflexiveClosureName, Seq(z, y) ++ fixedVars)))))
                } else {
                    val helperName = nameGen.freshName(functionName);
                    closureFunctions += FuncDecl(reflexiveClosureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool);
                    auxilaryFunctions += FuncDecl(helperName, Seq(sort, sort, sort) ++ fixedSorts, Sort.Bool);
                    val u = Var(nameGen.freshName("u"));
                    closureAxioms += Forall(avars ++ fixedArgVars, Not(App(helperName, Seq(x, x, y) ++ fixedVars)))
                    closureAxioms += Forall((avars :+ az :+ u.of(sort)) ++ fixedArgVars,
                        Implication(And(App(helperName, Seq(x, y, u) ++ fixedVars), App(helperName, Seq(y, z, u) ++ fixedVars)), App(helperName, Seq(x, z, u) ++ fixedVars)))
                    closureAxioms += Forall((avars :+ az) ++ fixedArgVars,
                        Implication(And(App(helperName, Seq(x, y, y) ++ fixedVars), App(helperName, Seq(y, z, z) ++ fixedVars), Not(Term.sortedEq(sort, x, z))), App(helperName, Seq(x, z, z) ++ fixedVars)))
                    closureAxioms += Forall((avars :+ az) ++ fixedArgVars,
                        Implication(And(App(helperName, Seq(x, y, z) ++ fixedVars), Not(Term.sortedEq(sort, y, z))), App(helperName, Seq(y, z, z) ++ fixedVars)))
                    closureAxioms += Forall(avars ++ fixedArgVars,
                        Implication(And(funcContains(functionName, x, y, fixedVars), Not(Term.sortedEq(sort, x, y))), App(helperName, Seq(x, y, y) ++ fixedVars)))
                    closureAxioms += Forall(avars ++ fixedArgVars,
                        Implication(App(helperName, Seq(x, y, y) ++ fixedVars), Exists(az, And(funcContains(functionName, x, z, fixedVars), App(helperName, Seq(x, z, y) ++ fixedVars)))))
                    closureAxioms += Forall(avars ++ fixedArgVars,
                        Iff(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), Or(App(helperName, Seq(x, y, y) ++ fixedVars), Term.sortedEq(sort, x, y))))
                    closureAxioms += Forall(avars ++ fixedArgVars,
                        Iff(App(closureName, Seq(x, y) ++ fixedVars), Exists(az, And(funcContains(functionName, x, z, fixedVars), App(reflexiveClosureName, Seq(z, y) ++ fixedVars)))))
                }
            }
            App(closureName, Seq(c.arg1, c.arg2) ++ c.fixedArgs).mapArguments(visit)
        }
        
        override def visitReflexiveClosure(rc: ReflexiveClosure): Term = {
            var functionName = rc.functionName
            val closureName = getClosureName(functionName)
            val reflexiveClosureName = getReflexiveClosureName(functionName)
            if (!queryFunction(reflexiveClosureName)) {
                val fixedSorts = getFixedSorts(functionName)
                val fixedVars = getFixedVars(fixedSorts.length)
                val fixedArgVars = fixedVars.zip(fixedSorts) map (pair => (pair._1.of(pair._2)))
                
                // Find the sort we are closing over
                val sort = getClosingSortOfFunction(functionName)
                // Record the sort as no longer being able change scope
                unchangingSorts += sort
                
                closureFunctions += FuncDecl(reflexiveClosureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val avars = Seq(x.of(sort), y.of(sort)) ++ fixedArgVars
                val z = Var(nameGen.freshName("z"))
                val az = z.of(sort)
                val scope = scopes(sort)

                
                if (scope.size > 100) {
                    val helperName = nameGen.freshName(functionName);
                    auxilaryFunctions += FuncDecl.mkFuncDecl(helperName, sort, sort, sort, Sort.Bool);
                    val u = Var(nameGen.freshName("u"));
                    closureAxioms += Forall(avars, Not(App(helperName, Seq(x, x, y) ++ fixedVars)))
                    closureAxioms += Forall(avars :+ az :+ u.of(sort), Implication(And(App(helperName, List(x, y, u) ++ fixedVars), App(helperName, List(y, z, u) ++ fixedVars)), App(helperName, List(x, z, u) ++ fixedVars)))
                    closureAxioms += Forall(avars :+ az, Implication(And(App(helperName, Seq(x, y, y) ++ fixedVars), App(helperName, Seq(y, z, z) ++ fixedVars), Not(Term.sortedEq(sort, x, z))), App(helperName, Seq(x, z, z) ++ fixedVars)))
                    closureAxioms += Forall(avars :+ az, Implication(And(App(helperName, Seq(x, y, z) ++ fixedVars), Not(Term.sortedEq(sort, y, z))), App(helperName, Seq(y, z, z) ++ fixedVars)))
                    closureAxioms += Forall(avars, Implication(And(funcContains(functionName, x, y, fixedVars), Not(Term.sortedEq(sort, x, y))), App(helperName, Seq(x, y, y) ++ fixedVars)))
                    closureAxioms += Forall(avars, Implication(App(helperName, Seq(x, y, y) ++ fixedVars), Exists(az, And(funcContains(functionName, x, z, fixedVars), App(helperName, Seq(x, z, y) ++ fixedVars)))))
                    closureAxioms += Forall(avars, Iff(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), Or(App(helperName, Seq(x, y, y) ++ fixedVars), Term.sortedEq(sort, x, y))))
                } else if (queryFunction(closureName)) {
                    closureAxioms += Forall(avars, Iff(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), Or(Term.sortedEq(sort, x, y), App(closureName, Seq(x, y) ++ fixedVars))))
                } else {
                    closureFunctions += FuncDecl(closureName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                    for (s <- 1 until scala.math.ceil(scala.math.log(scope.size)/scala.math.log(2)).toInt) {
                        val newFunctionName = nameGen.freshName(functionName);
                        auxilaryFunctions += FuncDecl(newFunctionName, Seq(sort, sort) ++ fixedSorts, Sort.Bool)
                        closureAxioms += Forall(avars, Iff(App(newFunctionName, Seq(x, y)  ++ fixedVars), Or(funcContains(functionName, x, y, fixedVars), Exists(az, And(funcContains(functionName, x, z, fixedVars), funcContains(functionName, z, y, fixedVars))))))
                        functionName = newFunctionName;
                    }
                    closureAxioms += Forall(avars, Iff(App(closureName, Seq(x, y) ++ fixedVars), Or(funcContains(functionName, x, y, fixedVars), Exists(az, And(funcContains(functionName, x, z, fixedVars), funcContains(functionName, z, y, fixedVars))))))
                    closureAxioms += Forall(avars, Iff(App(reflexiveClosureName, Seq(x, y) ++ fixedVars), Or(Term.sortedEq(sort, x, y), App(closureName, Seq(x, y) ++ fixedVars))))
                }
            }
            App(reflexiveClosureName, Seq(rc.arg1, rc.arg2) ++ rc.fixedArgs).mapArguments(visit)
        }
        
    }
}
