package fortress.solverinterface

import edu.stanford.CVC4.{
    ExprManager => CVC4ExprManager,
    Expr => CVC4Expr,
    SmtEngine => CVC4SmtEngine,
    Result => CVC4Result,
    Kind => CVC4Kind,
    Rational => CVC4Rational,
    BitVector => CVC4BitVector,
    vectorExpr => CVC4VectorExpr,
    vectorType => CVC4VectorType,
	Type => CVC4Type,
    FunctionType => CVC4FunctionType
}

import fortress.msfol._
import fortress.util.Errors

import scala.jdk.CollectionConverters._

class TheoryToCVC4(theory: Theory){
    System.loadLibrary("cvc4jni")
    val em = new CVC4ExprManager
    val smt = new CVC4SmtEngine(em)

    val sortConversionMap: Map[Sort, CVC4Type] = ( for(sort <- theory.sorts) yield
        (sort, sort match {
            case SortConst(name) => em mkSort sort.name
            case BoolSort => em.booleanType
            case IntSort => em.integerType
            case BitVectorSort(bitwidth) => em mkBitVectorType bitwidth
        })
    ).toMap
    
    val constantConversionMap: Map[AnnotatedVar, CVC4Expr] = ( for(cnst <- theory.constants) yield
        (cnst, em.mkVar(cnst.name, sortConversionMap apply cnst.getSort))
    ).toMap
    
    val funcConversionMap: Map[String, CVC4Expr] = ( for(decl <- theory.functionDeclarations) yield
        (decl.name, em.mkVar(decl.name, em.mkFunctionType(
                seqSortToVectorType(decl.argSorts),
                sortConversionMap.apply(decl.resultSort))))
    ).toMap

    def convert: CVC4SmtEngine = {
        smt
    }

    def convertExpr(term: Term): CVC4Expr = term match {
        case Top => em.mkConst(true)
        case Bottom => em.mkConst(false)
        case IntegerLiteral(value) => em.mkExpr(CVC4Kind.TO_INTEGER, em.mkConst(new CVC4Rational(value)))
        case BitVectorLiteral(value, bitwidth) => em.mkConst(new CVC4BitVector(bitwidth, value))
        case EnumValue(_) | DomainElement(_, _) => Errors.unreachable()
        case v @ Var(name) => ???
        case Not(body) => em.mkExpr(CVC4Kind.NOT, convertExpr(body))
        case AndList(args) => em.mkExpr(CVC4Kind.AND, seqTermToVectorExpr(args))
        case OrList(args) => em.mkExpr(CVC4Kind.OR, seqTermToVectorExpr(args))
        case Distinct(args) => em.mkExpr(CVC4Kind.DISTINCT, seqTermToVectorExpr(args))
        case Implication(left, right) => em.mkExpr(CVC4Kind.IMPLIES, convertExpr(left), convertExpr(right))
        case Iff(left, right) => em.mkExpr(CVC4Kind.EQUAL, convertExpr(left), convertExpr(right))
        case Eq(left, right) => em.mkExpr(CVC4Kind.EQUAL, convertExpr(left), convertExpr(right))
        case App(fname, args) => ???
        case Exists(vars, body) => ???
        case Forall(vars, body) => ???
        case BuiltinApp(fn, args) => ???
    }

    def seqTermToVectorExpr(seq: Seq[Term]) : CVC4VectorExpr = {
        val exprs = new CVC4VectorExpr
        seq.foreach(term => exprs.add(convertExpr(term)))
        exprs
    }
    
    def seqSortToVectorType(seq: Seq[Sort]) : CVC4VectorType = {
        val params = new CVC4VectorType
        seq.foreach(sort => params.add(sortConversionMap.apply(sort)))
        params
    }
}
