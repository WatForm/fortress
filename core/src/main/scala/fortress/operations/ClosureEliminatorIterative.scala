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

class ClosureEliminatorIterative(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Int], nameGen: NameGenerator) extends ClosureEliminator(topLevelTerm, signature, scopes, nameGen) {


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
            def queryFunction(name: String): Boolean = signature.hasFunctionWithName(name) || closureFunctions.exists(f => f.name == name)

            // If we have not generated the function yet
            if (!queryFunction(closureName)) {
                // Look at original function to make declaration for the closure function
                val rel = signature.queryUninterpretedFunction(functionName).get
                val sort = rel.argSorts(0)
                closureFunctions += FuncDecl.mkFuncDecl(closureName, sort, sort, Sort.Bool)
                val x = Var(nameGen.freshName("x"));
                val y = Var(nameGen.freshName("y"));

                val avars = List(x.of(sort), y.of(sort))
                val z = Var(nameGen.freshName("z"))
                val az = z.of(sort)
                val scope = scopes(sort)

                if (scope < 100) {
                    // Using the technique of repeated squaring
                    for (s <- 1 until scala.math.ceil(scala.math.log(scope)/scala.math.log(2)).toInt) {
                        // Make a new function with a similar name
                        val newFunctionName = nameGen.freshName(functionName);
                        // It uses the same arguments
                        closureFunctions += FuncDecl.mkFuncDecl(newFunctionName, sort, sort, Sort.Bool)
                        // For every input,
                        closureAxioms += Forall(avars, Iff(App(newFunctionName, Seq(x, y)), // For every inputs R_n+1(x,y) <=>
                            Or( // 1 of 2 things
                                funcContains(functionName, x, y), // R_n(x,y) already existed in the original
                                Exists(az, // There is some z where R_n(x,z) and R_n(z,y)
                                    And(
                                        funcContains(functionName, x, z), 
                                        funcContains(functionName, z, y)
                                    )   
                                ))))
                        functionName = newFunctionName;
                    }
                    closureAxioms += Forall(avars, Iff(App(closureName, Seq(x, y)), Or(funcContains(functionName, x, y), Exists(az, And(funcContains(functionName, x, z), funcContains(functionName, z, y))))))
                } else if (queryFunction(reflexiveClosureName)) {
                    // If we have the reflexive closure, just use that
                    // Reflexive closure R(x,y) <=> exists z: R(x,z) and R(z,y)
                    closureAxioms += Forall(avars, Iff(App(closureName, Seq(x, y)), Exists(az, And(funcContains(functionName, x, z), App(reflexiveClosureName, Seq(z, y))))))
                } else {
                    val helperName = nameGen.freshName(functionName);
                    closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, sort, sort, Sort.Bool);
                    closureFunctions += FuncDecl.mkFuncDecl(helperName, sort, sort, sort, Sort.Bool);
                    val u = Var(nameGen.freshName("u"));
                    closureAxioms += Forall(avars, Not(App(helperName, Seq(x, x) :+ y)))
                    closureAxioms += Forall(avars :+ az :+ u.of(sort), Implication(And(App(helperName, Seq(x, y) :+ u), App(helperName, Seq(y, z) :+ u)), App(helperName, Seq(x, z) :+ u)))
                    closureAxioms += Forall(avars :+ az, Implication(And(App(helperName, Seq(x, y) :+ y), App(helperName, Seq(y, z) :+ z), Not(Eq(x, z))), App(helperName, Seq(x, z) :+ z)))
                    closureAxioms += Forall(avars :+ az, Implication(And(App(helperName, Seq(x, y) :+ z), Not(Eq(y, z))), App(helperName, Seq(y, z) :+ z)))
                    closureAxioms += Forall(avars, Implication(And(funcContains(functionName, x, y), Not(Eq(x, y))), App(helperName, Seq(x, y) :+ y)))
                    closureAxioms += Forall(avars, Implication(App(helperName, Seq(x, y) :+ y), Exists(az, And(funcContains(functionName, x, z), App(helperName, Seq(x, z) :+ y)))))
                    closureAxioms += Forall(avars, Iff(App(reflexiveClosureName, Seq(x, y)), Or(App(helperName, Seq(x, y) :+ y), Eq(x, y))))
                    closureAxioms += Forall(avars, Iff(App(closureName, Seq(x, y)), Exists(az, And(funcContains(functionName, x, z), App(reflexiveClosureName, Seq(z, y))))))
                }
            }
            App(closureName, Seq(c.arg1, c.arg2)).mapArguments(visit)
        }
        
        override def visitReflexiveClosure(rc: ReflexiveClosure): Term = {
            var functionName = rc.functionName
            val closureName = getClosureName(functionName)
            val reflexiveClosureName = getReflexiveClosureName(functionName)
            if (!queryFunction(reflexiveClosureName)) {
                val rel = signature.queryUninterpretedFunction(functionName).get
                val sort = rel.argSorts(0)
                closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, sort, sort, Sort.Bool)
                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val avars = List(x.of(sort), y.of(sort))
                val z = Var(nameGen.freshName("z"))
                val az = z.of(sort)
                val scope = scopes(sort)
                def getVarList(v1: Var, v2: Var): List[Var] = List(v1, v2)
                if (scope > 100) {
                    val helperName = nameGen.freshName(functionName);
                    closureFunctions += FuncDecl.mkFuncDecl(helperName, sort, sort, sort, Sort.Bool);
                    val u = Var(nameGen.freshName("u"));
                    closureAxioms += Forall(avars, Not(App(helperName, getVarList(x, x) :+ y)))
                    closureAxioms += Forall(avars :+ az :+ u.of(sort), Implication(And(App(helperName, getVarList(x, y) :+ u), App(helperName, getVarList(y, z) :+ u)), App(helperName, getVarList(x, z) :+ u)))
                    closureAxioms += Forall(avars :+ az, Implication(And(App(helperName, getVarList(x, y) :+ y), App(helperName, getVarList(y, z) :+ z), Not(Eq(x, z))), App(helperName, getVarList(x, z) :+ z)))
                    closureAxioms += Forall(avars :+ az, Implication(And(App(helperName, getVarList(x, y) :+ z), Not(Eq(y, z))), App(helperName, getVarList(y, z) :+ z)))
                    closureAxioms += Forall(avars, Implication(And(funcContains(functionName, x, y), Not(Eq(x, y))), App(helperName, getVarList(x, y) :+ y)))
                    closureAxioms += Forall(avars, Implication(App(helperName, getVarList(x, y) :+ y), Exists(az, And(funcContains(functionName, x, z), App(helperName, getVarList(x, z) :+ y)))))
                    closureAxioms += Forall(avars, Iff(App(reflexiveClosureName, getVarList(x, y)), Or(App(helperName, getVarList(x, y) :+ y), Eq(x, y))))
                } else if (queryFunction(closureName)) {
                    closureAxioms += Forall(avars, Iff(App(reflexiveClosureName, getVarList(x, y)), Or(Eq(x, y), App(closureName, getVarList(x, y)))))
                } else {
                    closureFunctions += FuncDecl.mkFuncDecl(closureName, sort, sort, Sort.Bool)
                    for (s <- 1 until scala.math.ceil(scala.math.log(scope)/scala.math.log(2)).toInt) {
                        val newFunctionName = nameGen.freshName(functionName);
                        closureFunctions += FuncDecl.mkFuncDecl(newFunctionName, sort, sort, Sort.Bool)
                        closureAxioms += Forall(avars, Iff(App(newFunctionName, getVarList(x, y)), Or(funcContains(functionName, x, y), Exists(az, And(funcContains(functionName, x, z), funcContains(functionName, z, y))))))
                        functionName = newFunctionName;
                    }
                    closureAxioms += Forall(avars, Iff(App(closureName, getVarList(x, y)), Or(funcContains(functionName, x, y), Exists(az, And(funcContains(functionName, x, z), funcContains(functionName, z, y))))))
                    closureAxioms += Forall(avars, Iff(App(reflexiveClosureName, getVarList(x, y)), Or(Eq(x, y), App(closureName, getVarList(x, y)))))
                }
            }
            App(reflexiveClosureName, Seq(rc.arg1, rc.arg2)).mapArguments(visit)
        }
        
    }
}
