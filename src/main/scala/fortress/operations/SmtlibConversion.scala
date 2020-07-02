package fortress.operations

import fortress.msfol._
import fortress.util.Errors

class SmtlibConverter(writer: java.io.Writer) {
    // Use a writer for efficiency
    def write(t: Term): Unit = {
        def recur(term: Term): Unit = term match {
            case DomainElement(_, _) | EnumValue(_) =>
                Errors.unsupported("Domain elements and enum values cannot be converted to SMTLIB2")
            // case d @ DomainElement(index, sort) => writer.write(d.asSmtConstant.name)
            case Top => writer.write("true")
            case Bottom => writer.write("false")
            case Var(name) => writer.write(name)
            case Not(p) => writeGeneralApp("not", Seq(p))
            case AndList(args) => writeGeneralApp("and", args)
            case OrList(args) => writeGeneralApp("or", args)
            case Distinct(args) => writeGeneralApp("distinct", args)
            case Implication(left, right) => writeGeneralApp("=>", Seq(left, right))
            case Iff(left, right) => writeGeneralApp("=", Seq(left, right))
            case Eq(left, right) => writeGeneralApp("=", Seq(left, right))
            case App(fname, args) => writeGeneralApp(fname, args)
            case IfThenElse(condition, ifTrue, ifFalse) => writeGeneralApp("ite", Seq(condition, ifTrue, ifFalse))
            case Exists(vars, body) => {
                writer.write("(exists (")
                var num = 0
                for(av <- vars) {
                    if(num > 0) {
                        writer.write(' ')
                    }
                    writer.write('(')
                    writer.write(av.name)
                    writer.write(' ')
                    writeSort(av.sort)
                    writer.write(')')
                    num += 1
                }
                writer.write(") ")
                recur(body)
                writer.write(')')
            }
            case Forall(vars, body) => {
                writer.write("(forall (")
                var num = 0
                for(av <- vars) {
                    if(num > 0) {
                        writer.write(' ')
                    }
                    writer.write('(')
                    writer.write(av.name)
                    writer.write(' ')
                    writeSort(av.sort)
                    writer.write(')')
                    num += 1
                }
                writer.write(") ")
                recur(body)
                writer.write(')')
            }
            
            // Integers
            case IntegerLiteral(value) => {
                if(value >= 0) {
                    writer.write(value.toString)
                } else {
                    writeGeneralApp("-", Seq(IntegerLiteral(- value)))
                }
            }
            case BuiltinApp(IntPlus, args) => writeGeneralApp("+", args)
            case BuiltinApp(IntNeg, args) => writeGeneralApp("-", args)
            case BuiltinApp(IntSub, args) => writeGeneralApp("-", args)
            case BuiltinApp(IntMult, args) => writeGeneralApp("*", args)
            case BuiltinApp(IntDiv, args) => writeGeneralApp("div", args)
            case BuiltinApp(IntMod, args) => writeGeneralApp("mod", args)
            case BuiltinApp(IntLE, args) => writeGeneralApp("<=", args)
            case BuiltinApp(IntLT, args) => writeGeneralApp("<", args)
            case BuiltinApp(IntGE, args) => writeGeneralApp(">=", args)
            case BuiltinApp(IntGT, args) => writeGeneralApp(">", args)
            
            // BitVectors
            case BitVectorLiteral(value, bitwidth) => {
                // (_ bv10 32) is a bitvector of size 32 that representes the numeral 10
                // TODO what about negatives?
                writer.write("(_ bv")
                writer.write(value.toString)
                writer.write(' ')
                writer.write(bitwidth.toString)
                writer.write(')')
            }
            case BuiltinApp(BvPlus, args) => writeGeneralApp("bvadd", args)
            case BuiltinApp(BvNeg, args) => writeGeneralApp("bvneg", args)
            case BuiltinApp(BvSub, args) => writeGeneralApp("bvsub", args)
            case BuiltinApp(BvMult, args) => writeGeneralApp("bvmul", args)
            case BuiltinApp(BvSignedDiv, args) => writeGeneralApp("bvsdiv", args)
            case BuiltinApp(BvSignedRem, args) => writeGeneralApp("bvsrem", args)
            case BuiltinApp(BvSignedMod, args) => writeGeneralApp("bvsmod", args)
            case BuiltinApp(BvSignedLE, args) => writeGeneralApp("bvsle", args)
            case BuiltinApp(BvSignedLT, args) => writeGeneralApp("bvslt", args)
            case BuiltinApp(BvSignedGE, args) => writeGeneralApp("bvsge", args)
            case BuiltinApp(BvSignedGT, args) => writeGeneralApp("bvsgt", args)
        }
        
        def writeGeneralApp(functionName: String, args: Seq[Term]): Unit = {
            writer.write('(')
            writer.write(functionName)
            for(arg <- args) {
                writer.write(' ')
                recur(arg)
            }
            writer.write(')')
        }
        
        recur(t)
    }
    
    def writeSort(sort: Sort): Unit = sort match {
        case SortConst(name) => writer.write(name)
        case BoolSort => writer.write("Bool")
        case IntSort => writer.write("Int")
        case BitVectorSort(bitwidth) => {
            writer.write("(_ BitVec ")
            writer.write(bitwidth.toString)
            writer.write(')')
        }
    }
    
    def writeSorts(sorts: Seq[Sort]): Unit = {
        if(sorts.size == 1){
            writeSort(sorts.head)
        }
        else if(sorts.size > 1){
            writeSort(sorts.head)
            writer.write(' ')
            writeSorts(sorts.tail)
        }
    }
    
    def writeSortDecl(sort: Sort): Unit = {
        sort match {
            case SortConst(name) => {
                writer.write("(declare-sort ")
                writer.write(sort.name)
                writer.write(" 0)")
            }
            case _ =>
        }
    }
    
    def writeFuncDecl(funcDecl: FuncDecl): Unit = {
        writer.write("(declare-fun ")
        writer.write(funcDecl.name)
        writer.write(" (")
        writeSorts(funcDecl.argSorts)
        writer.write(") ")
        writeSort(funcDecl.resultSort)
        writer.write(')')
    }
    
    def writeConst(constant: AnnotatedVar): Unit = {
        writer.write("(declare-const ")
        writer.write(constant.name)
        writer.write(' ')
        writeSort(constant.getSort)
        writer.write(')')
    }

    def writeSignature(sig: Signature): Unit = {
        sig.sorts.foreach(writeSortDecl)
        sig.functionDeclarations.foreach(writeFuncDecl)
        sig.constants.foreach(writeConst)
    }
    
    def writeAssertion(term: Term): Unit = {
        writer.write("(assert ")
        write(term)
        writer.write(')')
    }
    
    def writeTheory(theory: Theory): Unit = {
        writeSignature(theory.signature)
        theory.axioms.foreach(writeAssertion)
    }
}
