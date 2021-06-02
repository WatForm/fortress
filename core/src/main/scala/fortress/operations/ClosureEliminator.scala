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
class ClosureEliminator(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Int], nameGen: NameGenerator) {
    val closureFunctions = scala.collection.mutable.Set[FuncDecl]()
    val closureAxioms = scala.collection.mutable.Set[Term]()
    val visitor = new ClosureVisitor
    
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
    
    class ClosureVisitor extends TermVisitorWithTypeContext[Term](signature) {
        
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
        
        override def visitClosure(c: Closure): Term = {
            var functionName = c.functionName
            val idx = c.arguments.indexOf(c.arg1)
            val closureName = "^" + idx + functionName
            val reflexiveClosureName = "*" + idx + functionName;
            def queryFunction(name: String): Boolean = signature.hasFunctionWithName(name) || closureFunctions.exists(f => f.name == name)
            if (!queryFunction(closureName)) {
                val rel = signature.queryUninterpretedFunction(functionName).get
                var argSorts = new ArrayList(rel.argSorts.asJava)
                val sort = argSorts.get(idx)
                closureFunctions += FuncDecl.mkFuncDecl(closureName, argSorts, Sort.Bool)
                val vars = List.tabulate(argSorts.size-2)(_ => Var(nameGen.freshName("bv")))
                val x = Var(nameGen.freshName("x"))
                val y = Var(nameGen.freshName("y"))
                val avars = (List.tabulate(idx)(i => vars(i).of(argSorts.get(i))) :+ x.of(sort) :+ y.of(sort)) ::: List.tabulate(vars.size-idx)(i => vars(idx+i).of(argSorts.get(idx+i+2)))
                val z = Var(nameGen.freshName("z"))
                val az = z.of(sort)
                val scope = scopes(sort)
                def getVarList(v1: Var, v2: Var): List[Var] = (vars.slice(0, idx) :+ v1 :+ v2) ::: vars.slice(idx+2, vars.size)
                if (scope < 100) {
                    for (s <- 1 until scala.math.ceil(scala.math.log(scope)/scala.math.log(2)).toInt) {
                        val newFunctionName = nameGen.freshName(functionName);
                        closureFunctions += FuncDecl.mkFuncDecl(newFunctionName, argSorts, Sort.Bool)
                        closureAxioms += Forall(avars, Iff(App(newFunctionName, getVarList(x, y)), Or(App(functionName, getVarList(x, y)), Exists(az, And(App(functionName, getVarList(x, z)), App(functionName, getVarList(z, y)))))))
                        functionName = newFunctionName;
                    }
                    closureAxioms += Forall(avars, Iff(App(closureName, getVarList(x, y)), Or(App(functionName, getVarList(x, y)), Exists(az, And(App(functionName, getVarList(x, z)), App(functionName, getVarList(z, y)))))))
                } else if (queryFunction(reflexiveClosureName)) {
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
            val reflexiveClosureName = "*" + idx + functionName
            val closureName = "^" + idx + functionName;
            def queryFunction(name: String): Boolean = signature.hasFunctionWithName(name) || closureFunctions.exists(f => f.name == name)
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
        
        override def visitForallInner(term: Forall): Term = term.mapBody(visit)
        
        override def visitExistsInner(term: Exists): Term = term.mapBody(visit)
        
        override def visitDomainElement(d: DomainElement): Term = d
        
        override def visitIntegerLiteral(literal: IntegerLiteral): Term = literal
        
        override def visitBitVectorLiteral(literal: BitVectorLiteral): Term = literal
        
        override def visitEnumValue(e: EnumValue): Term = e

        override def visitIfThenElse(ite: IfThenElse): Term = IfThenElse(visit(ite.condition), visit(ite.ifTrue), visit(ite.ifFalse))
    }
}