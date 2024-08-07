package fortress.msfol
import fortress.operations.TermOps._
import fortress.operations.TypeCheckResult

case class ConstantDefinition(avar: AnnotatedVar, body: Term) {
    val name = avar.name
    val variable = avar.variable
    val sort = avar.sort

    override def toString: String = {f"ConstantDefinition(${avar}, ${body})"}

    def mapBody(f: Term => Term): ConstantDefinition = copy(body = f(body))

    def asAxiom: Term = {
        if(sort == BoolSort) {
            Iff(variable, body)
        } else {
            Eq(variable, body)
        }
    }
}

object ConstantDefinition{
    def mkConstantDefinition(avar: AnnotatedVar, body: Term): ConstantDefinition =  {
        ConstantDefinition(avar, body)
    }
}