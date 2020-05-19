package fortress.operations

import fortress.msfol._
import fortress.util.Errors

object SmtlibConverter {
    // Use a writer for efficiency
    def write(t: Term, writer: java.io.Writer): Unit = {
        def recur(term: Term): Unit = term match {
            case DomainElement(_, _) | EnumValue(_) | IntegerLiteral(_) |
                BuiltinApp(_, _) | BitVectorLiteral(_, _) => ???
            case Top => writer.write("true")
            case Bottom => writer.write("false")
            case Var(name) => writer.write(name)
            case Not(p) => {
                writer.write("(not ")
                recur(p)
                writer.write(')')
            }
            case AndList(args) => {
                writer.write("(and")
                for(arg <- args) {
                    writer.write(' ')
                    recur(arg)
                }
                writer.write(')')
            }
            case OrList(args) => {
                writer.write("(or")
                for(arg <- args) {
                    writer.write(' ')
                    recur(arg)
                }
                writer.write(')')
            }
            case Distinct(args) => {
                writer.write("(distinct")
                for(arg <- args) {
                    writer.write(' ')
                    recur(arg)
                }
                writer.write(')')
            }
            case Implication(left, right) => {
                writer.write("(=> ")
                recur(left)
                writer.write(' ')
                recur(right)
                writer.write(')')
            }
            case Iff(left, right) => {
                writer.write("(= ")
                recur(left)
                writer.write(' ')
                recur(right)
                writer.write(')')
            }
            case Eq(left, right) => {
                writer.write("(= ")
                recur(left)
                writer.write(' ')
                recur(right)
                writer.write(')')
            }
            case App(fname, args) => {
                writer.write('(')
                writer.write(fname)
                for(arg <- args) {
                    writer.write(' ')
                    recur(arg)
                }
                writer.write(')')
            }
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
                    writer.write(av.sort.name)
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
                    writer.write(av.sort.name)
                    writer.write(')')
                    num += 1
                }
                writer.write(") ")
                recur(body)
                writer.write(')')
            }
        }
        recur(t)
    }
}
