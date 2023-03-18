package fortress.msfol
import fortress.operations.TermOps._
import fortress.operations.TypeCheckResult

case class ConstantDefinition(avar: AnnotatedVar, body: Term) {
    val name = avar.name
    val variable = avar.variable
    val sort = avar.sort

    override def toString: String = {f"ConstantDefinition(${avar}, ${body})"}
}