package fortress.operations

import fortress.msfol._
import fortress.util.Errors
import fortress.util.NameConverter._

class PythonZ3Converter(writer: java.io.Writer) {
    // TODO hoisting? would that work here? maybe use a string builder?
    // We would probably convert writer to have the recursion and other steps inside it?

    // Writer is used for efficiency (don't keep building strings)
    def writeTerm(term: Term): Unit = term match {
        case EnumValue(name) => writer.write(nameWithAffix(name))
        case Top => writer.write("True()")
        case Bottom => writer.write("False()")
        case Var(name) => writer.write(nameWithAffix(name))
        case Not(p) => writeGeneralApp("Not", p)
        case AndList(args) => writeGeneralApp("And", args)
        case OrList(args) => writeGeneralApp("Or", args)
        case Distinct(args) => writeGeneralApp("Distinct", args)
        case Implication(left, right) => writeGeneralApp("Implies", Seq(left, right))
        // (left == right)
        case Iff(left, right) => writeBinOp("==", left, right)
        case Eq(left, right) => writeBinOp("==", left, right)
        case App(fname, args) => writeGeneralApp(nameWithAffix(fname), args)
        case IfThenElse(condition, ifTrue, ifFalse) => writeGeneralApp("If", Seq(ifTrue, ifFalse))
        case Exists(vars, body) => writeQuantifier("Exists", vars, body)
        case Forall(vars, body) => writeQuantifier("ForAll", vars, body)
        // Integers
        case IntegerLiteral(value) => writer.write(value.toString())
        // Skipping

        case x => Errors.Internal.preconditionFailed("Not implemented for translating to z3: " + x.toString())

    }

    // Write the application of a function (or similar)
    def writeGeneralApp(functionName: String, args: Seq[Term]): Unit = {
        writer.write(functionName)
        writer.write("(")
        for (arg <- args){
            writeTerm(arg)
            // The terminal , is valid Python
            writer.write(", ")
        }
        writer.write(")")
    }

    def writeGeneralApp(functionName: String, arg: Term): Unit = {
        writer.write(functionName)
        writer.write("(")
        writeTerm(arg)
        writer.write(")")
    }

    /**
      * Writes a function with the first arg being a string (typically the name being assigned).
      * 
      * `writeNamedPyFunction("DeclareSort", "f", Top)` writes `DeclareSort('f', True())`
      * @param functionName
      * @param name
      * @param args
      */
    def writeNamedPyFunction(functionName: String, name: String, args: Seq[Any]): Unit = {
        writer.write(functionName)
        writer.write("('")
        writer.write(name)
        writer.write("'")
        for (arg <- args){
            writer.write(", ")
            write(arg)
        }
        writer.write(")")
    }


    def writeNamedPyFunction(functionName: String, name: String, arg: Any): Unit = {
        writer.write(functionName)
        writer.write("('")
        writer.write(name)
        writer.write("', ")
        write(arg)
        writer.write(")")
    }

    def writeNamedPyFunction(functionName: String, name: String): Unit = {
        writer.write(functionName)
        writer.write("('")
        writer.write(name)
        writer.write("')")
    }

    //
    def writeQuantifier(name: String, vars: Seq[AnnotatedVar], body: Term): Unit = {
        writer.write(name)
        writer.write("([")
        for (var_ <- vars){
            writer.write(nameWithAffix(var_.name))
            writer.write(", ")
        }
        writer.write("], ")
        writeTerm(body)
        writer.write(")")
    }

    def writeBinOp(op: String, left: Term, right: Term): Unit = {
        writer.write("((")
        writeTerm(left)
        writer.write(") == (")
        writeTerm(right)
        writer.write("))")
    }

    // NOTE affixing sort names?
    def writeSort(sort: Sort): Unit = sort match {
        case SortConst(name) => writer.write(nameWithAffix(name))
        case BoolSort => writer.write("BoolSort()")
        case IntSort => writer.write("IntSort()")
        case BitVectorSort(bitwidth) => writer.write("BitVecSort("); writer.write(bitwidth.toString()); writer.write(")")
    }

    // NOTE should we include \n?
    
    def writeSortDecl(sort: Sort): Unit = sort match {
        case SortConst(name) => {
            var z3name = nameWithAffix(name)
            writer.write(z3name)
            writer.write(" = ")
            writeNamedPyFunction("DeclareSort", z3name)
            writer.write('\n')
        }
        case _ => // do nothing
    }

    def writeFuncDecl(funcDecl: FuncDecl): Unit = {
        var z3name = nameWithAffix(funcDecl.name)
        writer.write(z3name)
        writer.write(" = ")
        writeNamedPyFunction("Function", z3name, funcDecl.argSorts)
        writer.write('\n')
    }

    def writeConstDecl(constant: AnnotatedVar): Unit = constant match {
        case AnnotatedVar(name, sort) => {
            val z3name = nameWithAffix(constant.name)
            writer.write(z3name)
            writer.write(" = ")
            writeNamedPyFunction("ConstDecl", z3name, sort)
            writer.write('\n')
        } 
    }

    def writeEnumDecl(sort: Sort, enums: Seq[EnumValue]): Unit = {
        val sortName = nameWithAffix(sort.name)
        val enumNames = enums.map(v => nameWithAffix(v.name))
        
        // Of the form
        // Color, (red, green, blue) = EnumSort('Color', ['red','green','blue'])
        writer.write(sortName)
        writer.write(", (")
        for (name <- enumNames) {
            writer.write(name)
            writer.write(", ")
        }
        writer.write(") = EnumSort('")
        writer.write(sortName)
        writer.write("', [")
        for (name <- enumNames) {
            writer.write(name)
            writer.write(", ")
        }
        writer.write("])\n")
    }

    def writeSignature(sig: Signature): Unit = {
        sig.sorts.removedAll(sig.enumConstants.keys).foreach(writeSortDecl)
        sig.enumConstants.foreach(x => writeEnumDecl(x._1, x._2))
        sig.functionDeclarations.foreach(writeFuncDecl)
        sig.constants.foreach(writeConstDecl)
    }

    def writeAssertion(term: Term): Unit = {
        writer.write("__solver.add(")
        writeTerm(term)
        writer.write(")\n")
    }

    def writeTheory(theory: Theory): Unit = {
        writeSignature(theory.signature)
        writer.write("__solver = Solver()")
        theory.axioms.foreach(writeAssertion)
    }

    // We need to declare consts as well as use them, may need separate functions?
    // Or do we need to treat vars as consts?
    /*
    def writeConst(constant: AnnotatedVar): Unit = constant match {
        case AnnotatedVar(v, BoolSort) =>
    }
    */
    def write(value: Any): Unit = value match {
        case x: Term => writeTerm(x)
        case x: Sort => writeSort(x)
    }

}