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
            // TODO ??
            val idx = c.arguments.indexOf(c.arg1)
            // The name that this closure will have (idx specific)
            val closureName = getClosureName(functionName, idx.toString())
            val reflexiveClosureName = getReflexiveClosureName(functionName, idx.toString())

            // Function that checks if the function already exists or we have generated it
            def queryFunction(name: String): Boolean = signature.hasFunctionWithName(name) || closureFunctions.exists(f => f.name == name)

            // If we have not generated the function yet
            if (!queryFunction(closureName)) {
                // Look at original function to make declaration for the closure function
                val rel = signature.queryUninterpretedFunction(functionName).get
                var argSorts = new ArrayList(rel.argSorts.asJava)
                val sort = argSorts.get(idx)
                closureFunctions += FuncDecl.mkFuncDecl(closureName, argSorts, Sort.Bool)
                // TODO ??
                val vars = List.tabulate(argSorts.size-2)(_ => Var(nameGen.freshName("bv")));
                val x = Var(nameGen.freshName("x"));
                val y = Var(nameGen.freshName("y"));

                val avars = (List.tabulate(idx)(i => vars(i).of(argSorts.get(i))) :+ x.of(sort) :+ y.of(sort)) ::: (List.tabulate(vars.size-idx)(i => vars(idx+i).of(argSorts.get(idx+i+2))))
                val z = Var(nameGen.freshName("z"))
                val az = z.of(sort)
                val scope = scopes(sort)
                // ?? Is this just replacing the two we are checkign with ex R(a,b,c,x,y) we can close on xy?
                // Why do we assume they are adjacent? Partial application?
                def getVarList(v1: Var, v2: Var): List[Var] = (vars.slice(0, idx) :+ v1 :+ v2) ::: vars.slice(idx+2, vars.size)
                if (scope < 100) {
                    // Using the technique of repeated squaring
                    for (s <- 1 until scala.math.ceil(scala.math.log(scope)/scala.math.log(2)).toInt) {
                        // Make a new function with a similar name
                        val newFunctionName = nameGen.freshName(functionName);
                        // It uses the same arguments
                        closureFunctions += FuncDecl.mkFuncDecl(newFunctionName, argSorts, Sort.Bool)
                        // For every input,
                        closureAxioms += Forall(avars, Iff(App(newFunctionName, getVarList(x, y)), // For every inputs R_n+1(x,y) <=>
                            Or( // 1 of 2 things
                                App(functionName, getVarList(x, y)), // R_n(x,y) already existed in the original
                                Exists(az, // There is some z where R_n(x,z) and R_n(z,y)
                                    And(
                                        App(functionName, getVarList(x, z)), 
                                        App(functionName, getVarList(z, y))
                                    )   
                                ))))
                        functionName = newFunctionName;
                    }
                    closureAxioms += Forall(avars, Iff(App(closureName, getVarList(x, y)), Or(App(functionName, getVarList(x, y)), Exists(az, And(App(functionName, getVarList(x, z)), App(functionName, getVarList(z, y)))))))
                } else if (queryFunction(reflexiveClosureName)) {
                    // If we have the reflexive closure, just use that
                    // Reflexive closure R(x,y) <=> exists z: R(x,z) and R(z,y)
                    closureAxioms += Forall(avars, Iff(App(closureName, getVarList(x, y)), Exists(az, And(App(functionName, getVarList(x, z)), App(reflexiveClosureName, getVarList(z, y))))))
                } else {
                    val helperName = nameGen.freshName(functionName);
                    closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, argSorts, Sort.Bool);
                    argSorts.add(sort)
                    closureFunctions += FuncDecl.mkFuncDecl(helperName, argSorts, Sort.Bool);
                    val u = Var(nameGen.freshName("u"));
                    closureAxioms += Forall(avars, Not(App(helperName, getVarList(x, x) :+ y)))
                    closureAxioms += Forall(avars :+ az :+ u.of(sort), Implication(And(App(helperName, getVarList(x, y) :+ u), App(helperName, getVarList(y, z) :+ u)), App(helperName, getVarList(x, z) :+ u)))
                    closureAxioms += Forall(avars :+ az, Implication(And(App(helperName, getVarList(x, y) :+ y), App(helperName, getVarList(y, z) :+ z), Not(Eq(x, z))), App(helperName, getVarList(x, z) :+ z)))
                    closureAxioms += Forall(avars :+ az, Implication(And(App(helperName, getVarList(x, y) :+ z), Not(Eq(y, z))), App(helperName, getVarList(y, z) :+ z)))
                    closureAxioms += Forall(avars, Implication(And(App(functionName, getVarList(x, y)), Not(Eq(x, y))), App(helperName, getVarList(x, y) :+ y)))
                    closureAxioms += Forall(avars, Implication(App(helperName, getVarList(x, y) :+ y), Exists(az, And(App(functionName, getVarList(x, z)), App(helperName, getVarList(x, z) :+ y)))))
                    closureAxioms += Forall(avars, Iff(App(reflexiveClosureName, getVarList(x, y)), Or(App(helperName, getVarList(x, y) :+ y), Eq(x, y))))
                    closureAxioms += Forall(avars, Iff(App(closureName, getVarList(x, y)), Exists(az, And(App(functionName, getVarList(x, z)), App(reflexiveClosureName, getVarList(z, y))))))
                }
            }
            App(closureName, c.arguments).mapArguments(visit)
        }
        
        override def visitReflexiveClosure(rc: ReflexiveClosure): Term = {
            var functionName = rc.functionName
            val idx = rc.arguments.indexOf(rc.arg1)
            val closureName = getClosureName(functionName, idx.toString())
            val reflexiveClosureName = getReflexiveClosureName(functionName, idx.toString())
            if (!queryFunction(reflexiveClosureName)) {
                val rel = signature.queryUninterpretedFunction(functionName).get
                var argSorts = new ArrayList(rel.argSorts.asJava)
                val sort = argSorts.get(idx)
                closureFunctions += FuncDecl.mkFuncDecl(reflexiveClosureName, argSorts, Sort.Bool)
                val vars = List.tabulate(argSorts.size-2)(_ => Var(nameGen.freshName("bv")))
                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val avars = (List.tabulate(idx)(i => vars(i).of(argSorts.get(i))) :+ x.of(sort) :+ y.of(sort)) ::: List.tabulate(vars.size-idx)(i => vars(idx+i).of(argSorts.get(idx+i+2))) 
                val z = Var(nameGen.freshName("z"))
                val az = z.of(sort)
                val scope = scopes(sort)
                def getVarList(v1: Var, v2: Var): List[Var] = (vars.slice(0, idx) :+ v1 :+ v2) ::: vars.slice(idx+2, vars.size)
                if (scope > 100) {
                    val helperName = nameGen.freshName(functionName);
                    argSorts.add(sort)
                    closureFunctions += FuncDecl.mkFuncDecl(helperName, argSorts, Sort.Bool);
                    val u = Var(nameGen.freshName("u"));
                    closureAxioms += Forall(avars, Not(App(helperName, getVarList(x, x) :+ y)))
                    closureAxioms += Forall(avars :+ az :+ u.of(sort), Implication(And(App(helperName, getVarList(x, y) :+ u), App(helperName, getVarList(y, z) :+ u)), App(helperName, getVarList(x, z) :+ u)))
                    closureAxioms += Forall(avars :+ az, Implication(And(App(helperName, getVarList(x, y) :+ y), App(helperName, getVarList(y, z) :+ z), Not(Eq(x, z))), App(helperName, getVarList(x, z) :+ z)))
                    closureAxioms += Forall(avars :+ az, Implication(And(App(helperName, getVarList(x, y) :+ z), Not(Eq(y, z))), App(helperName, getVarList(y, z) :+ z)))
                    closureAxioms += Forall(avars, Implication(And(App(functionName, getVarList(x, y)), Not(Eq(x, y))), App(helperName, getVarList(x, y) :+ y)))
                    closureAxioms += Forall(avars, Implication(App(helperName, getVarList(x, y) :+ y), Exists(az, And(App(functionName, getVarList(x, z)), App(helperName, getVarList(x, z) :+ y)))))
                    closureAxioms += Forall(avars, Iff(App(reflexiveClosureName, getVarList(x, y)), Or(App(helperName, getVarList(x, y) :+ y), Eq(x, y))))
                } else if (queryFunction(closureName)) {
                    closureAxioms += Forall(avars, Iff(App(reflexiveClosureName, getVarList(x, y)), Or(Eq(x, y), App(closureName, getVarList(x, y)))))
                } else {
                    closureFunctions += FuncDecl.mkFuncDecl(closureName, argSorts, Sort.Bool)
                    for (s <- 1 until scala.math.ceil(scala.math.log(scope)/scala.math.log(2)).toInt) {
                        val newFunctionName = nameGen.freshName(functionName);
                        closureFunctions += FuncDecl.mkFuncDecl(newFunctionName, argSorts, Sort.Bool)
                        closureAxioms += Forall(avars, Iff(App(newFunctionName, getVarList(x, y)), Or(App(functionName, getVarList(x, y)), Exists(az, And(App(functionName, getVarList(x, z)), App(functionName, getVarList(z, y)))))))
                        functionName = newFunctionName;
                    }
                    closureAxioms += Forall(avars, Iff(App(closureName, getVarList(x, y)), Or(App(functionName, getVarList(x, y)), Exists(az, And(App(functionName, getVarList(x, z)), App(functionName, getVarList(z, y)))))))
                    closureAxioms += Forall(avars, Iff(App(reflexiveClosureName, getVarList(x, y)), Or(Eq(x, y), App(closureName, getVarList(x, y)))))
                }
            }
            App(reflexiveClosureName, rc.arguments).mapArguments(visit)
        }
        
    }
}
