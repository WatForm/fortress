package fortress.operations

import fortress.msfol._
import fortress.util.Errors
import fortress.util.NameConverter._
import java.sql.Ref

class SmtlibConverter(writer: java.io.Writer) {

    // Use a writer for efficiency
    def write(t: Term): Unit = {
        def recur(term: Term): Unit = term match {
            case DomainElement(_, _) =>
                Errors.Internal.preconditionFailed("Domain elements cannot be converted to SMTLIB2")
            // case d @ DomainElement(index, sort) => writer.write(d.asSmtConstant.name)
            case EnumValue(name) => writer.write(nameWithQuote(name))
            case Top => writer.write("true")
            case Bottom => writer.write("false")
            case Var(name) => writer.write(nameWithQuote(name))
            case Not(p) => writeGeneralApp("not", Seq(p))
            case AndList(args) => writeGeneralApp("and", args)
            case OrList(args) => writeGeneralApp("or", args)
            case Distinct(args) => writeGeneralApp("distinct", args)
            case Implication(left, right) => writeGeneralApp("=>", Seq(left, right))
            case Iff(left, right) => writeGeneralApp("=", Seq(left, right))
            case Eq(left, right) => writeGeneralApp("=", Seq(left, right))
            case App(fname, args) => writeGeneralApp(nameWithQuote(fname), args)
            case IfThenElse(condition, ifTrue, ifFalse) => writeGeneralApp("ite", Seq(condition, ifTrue, ifFalse))
            case Exists(vars, body) => {
                writer.write("(exists (")
                var num = 0
                for(av <- vars) {
                    if(num > 0) {
                        writer.write(' ')
                    }
                    writer.write('(')
                    writer.write(nameWithQuote(av.name))
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
                    writer.write(nameWithQuote(av.name))
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
                // We use signed bitvectors, so we can just use bvneg and the absolute value 
                val isNegative = value < 0
                val absValue = value.abs.toInt
                if (isNegative) {
                    writer.write("(bvneg")
                }
                writer.write("(_ bv")
                writer.write(absValue.toString())
                writer.write(' ')
                writer.write(bitwidth.toString)
                writer.write(')')
                if (isNegative){
                    writer.write(')')
                }
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
            case BuiltinApp(BvConcat, args) => writeGeneralApp("concat", args)
            case BuiltinApp(CastBVToInt, args) => writeGeneralApp("bv2int", args)
            case BuiltinApp(CastIntToBV(bitwidth), args) => writeGeneralApp(s"(_ int2bv $bitwidth)", args)


            case Closure(_, _, _, _) => Errors.Internal.impossibleState("Cannot convert Closure to smtlib")
            case ReflexiveClosure(_, _, _, _) =>  Errors.Internal.impossibleState("Cannot convert Reflexive Closure to smtlib")
        }
        
        // Does NOT do quoting on its own
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
        case SortConst(name) => writer.write(nameWithQuote(name))
        case BoolSort => writer.write("Bool")
        case IntSort => writer.write("Int")
        case UnBoundedIntSort => writer.write("Int")
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
                writer.write(nameWithQuote(sort.name))
                writer.write(" 0)\n")
            }
            case _ =>
        }
    }
    
    def writeFuncDecl(funcDecl: FuncDecl): Unit = {
        writer.write("(declare-fun ")
        writer.write(nameWithQuote(funcDecl.name))
        writer.write(" (")
        writeSorts(funcDecl.argSorts)
        writer.write(") ")
        writeSort(funcDecl.resultSort)
        writer.write(")\n")
    }

    /*
        (define-fun min ((x Int) (y Int)) Int
        (ite (< x y) x y))
     */
    def writeFunctionDefinition(funcDef: FunctionDefinition): Unit = {
        writer.write("(define-fun ")
        writer.write(nameWithQuote(funcDef.name))
        writer.write(" (")
//        writeArgSortedVars(funcDef.argSortedVar)
        funcDef.argSortedVar.foreach(writeArgSortedVar)
        writer.write(") ")
        writeSort(funcDef.resultSort)
        writer.write(" ")
        write(funcDef.body)
        writer.write(")\n")
    }

    def writeArgSortedVar(arg: AnnotatedVar): Unit = {
        writer.write("(")
        writer.write(nameWithQuote(arg.variable.name))
        writer.write(" ")
        writeSort(arg.sort)
        writer.write(") ")
    }

    def writeArgSortedVars(args: Seq[AnnotatedVar]): Unit = {
        args.foreach(writeArgSortedVar)
    }
    
    def writeConst(constant: AnnotatedVar): Unit = {
        writer.write("(declare-const ")
        writer.write(nameWithQuote(constant.name))
        writer.write(' ')
        writeSort(constant.sort)
        writer.write(")\n")
    }

    def writeConstDefn(cDef: ConstantDefinition): Unit = {
        writer.write("(define-fun ")
        writer.write(nameWithQuote(cDef.name))
        writer.write(" () ")
        writeSort(cDef.sort)
        writer.write(' ')
        write(cDef.body)
        writer.write(")\n")
    }

    def writeEnumConst(sort: Sort, enums: Seq[EnumValue]): Unit = {
        writer.write("(declare-datatypes () ((")
        writeSort(sort)
        enums.foreach(enumEntry => writer.write(' ' + nameWithQuote(enumEntry.name)))
        writer.write(")))\n")
    }

    /**
      * Definitions can be dependent on other definitions. So long as we don't introduce circular dependencies, we can order them and write them out.
      *
      * @param constantDefinitions
      * @param functionDefinitions
      */
    def writeDefinitions(definitions: Seq[Either[ConstantDefinition, FunctionDefinition]]): Unit = {
        definitions.foreach{
            case Left(cDef) => writeConstDefn(cDef)
            case Right(fDef) => writeFunctionDefinition(fDef)
        }
    }

    def writeSignature(sig: Signature): Unit = {
        sig.sorts.removedAll(sig.enumConstants.keys).foreach(writeSortDecl)
        sig.enumConstants.foreach(x => writeEnumConst(x._1, x._2))
        sig.functionDeclarations.foreach(writeFuncDecl)
        sig.constantDeclarations.foreach(writeConst)
        // TODO definitions of all kinds can be dependant on other definitions, we need to properly sort these somehow
        //sig.constantDefinitions.foreach(writeConstDefn)
        // We can use constants in function definitions so they must be later
        //sig.functionDefinitions.foreach(writeFunctionDefinition)
        writeDefinitions(sig.definitionsInDependencyOrder)
    }
    
    def writeAssertion(term: Term): Unit = {
        writer.write("(assert ")
        write(term)
        writer.write(")\n")
    }
    
    def writeTheory(theory: Theory): Unit = {
        writeSignature(theory.signature)
        theory.axioms.foreach(writeAssertion)
    }
}
