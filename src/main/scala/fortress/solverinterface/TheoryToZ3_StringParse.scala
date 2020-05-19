package fortress.solverinterface

import com.microsoft.z3.{
    Context => Z3Context,
    Solver => Z3Solver,
    Sort => Z3Sort,
    FuncDecl => Z3FuncDecl,
    Expr => Z3Expr,
    BoolExpr => Z3BoolExpr,
    ArithExpr => Z3ArithExpr,
    BitVecExpr => Z3BitVecExpr,
    IntExpr => Z3IntExpr,
    Symbol => Z3Symbol
}

import fortress.msfol._
import fortress.operations.TermOps._
import fortress.operations.TermVisitorWithTypeContext

import scala.jdk.CollectionConverters._

import fortress.util.Errors

// Precondition: theory must be typechecked and all declarations must
// be internally consistent
class TheoryToZ3_StringParse(theory: Theory) {
    
    val config = Map(
        "model" -> "true" // How does this affect performance?
    )
    val context = new Z3Context(config.asJava)
    
    def sortConversions(s: Sort): Z3Sort = s match {
        case SortConst(name) => context.mkUninterpretedSort(name)
        case BoolSort => context.getBoolSort
        case IntSort => context.getIntSort
        case BitVectorSort(bitwidth) => context.mkBitVecSort(bitwidth)
    }
    
    val constantConversionsMap: Map[String, Z3FuncDecl] = {
        val tuples = for(constant <- theory.constants) yield {
            val z3Sort = sortConversions(constant.sort)
            val z3Decl = context.mkConstDecl(constant.name, z3Sort)
            (constant.name, z3Decl)
        }
        tuples.toMap
    }
    
    def fdecltoZ3Decl(fdecl: FuncDecl): Z3FuncDecl = {
        val z3ArgSorts: Array[Z3Sort] = fdecl.argSorts.map(sortConversions).toArray
        val z3ResultSort = sortConversions(fdecl.resultSort)
        val z3Decl = context.mkFuncDecl(fdecl.name, z3ArgSorts, z3ResultSort)
        z3Decl
    }
    
    val functionConversionsMap: Map[String, Z3FuncDecl] = {
        val tuples = for(fdecl <- theory.functionDeclarations) yield (fdecl.name, fdecltoZ3Decl(fdecl))
        tuples.toMap
    }
    
    val sorts: Array[Z3Sort] = theory.sorts.filter(!_.isBuiltin).map(sortConversions).toArray
    val sortNames: Array[Z3Symbol] = sorts.map(_.getName())
    
    val decls: Array[Z3FuncDecl] = (
        theory.constants.map(av => constantConversionsMap(av.name)) ++
        theory.functionDeclarations.map(fdecltoZ3Decl)
    ).toArray
    val declNames: Array[Z3Symbol] = decls.map(_.getName())
    
    def convert: (Z3Context, Z3Solver) = {
        val solver  = context.mkSolver("QF_UFNIA") // How does changing the logic affect the efficiency?
        
        for(axiom <- theory.axioms) {
            // val formula: Array[Z3BoolExpr] = convertAxiom(axiom)
            // // val formula: Z3BoolExpr = convertAxiom(axiom).asInstanceOf[Z3BoolExpr]
            // Errors.assertion(formula.length == 1)
            solver.add(convertAxiom(axiom))
        }
        
        (context, solver)
    }
    
    def convertAxiom(axiom: Term): Z3BoolExpr = {
        val formula: Array[Z3BoolExpr] = context.parseSMTLIB2String(
            axiom.smtlibAssertion,
            sortNames,
            sorts,
            declNames,
            decls
        )
        Errors.assertion(formula.length == 1)
        formula.head
    }
}
