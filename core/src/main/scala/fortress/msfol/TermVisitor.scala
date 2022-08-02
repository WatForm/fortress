package fortress.msfol

import fortress.msfol._

/** A visitor for term syntax trees. */
trait TermVisitor[T] {
    def visit(term: Term): T = term.accept(this)

    def visitTop(): T
    def visitBottom(): T
    def visitVar(term: Var): T
    def visitEnumValue(term: EnumValue): T
    def visitDomainElement(term: DomainElement): T
    def visitNot(term: Not): T
    def visitAndList(term: AndList): T
    def visitOrList(term: OrList): T
    def visitDistinct(term: Distinct): T
    def visitImplication(term: Implication): T
    def visitIff(term: Iff): T
    def visitEq(term: Eq): T
    def visitApp(term: App): T
    def visitBuiltinApp(term: BuiltinApp): T
    def visitExists(term: Exists): T
    def visitForall(term: Forall): T
    def visitIntegerLiteral(term: IntegerLiteral): T
    def visitBitVectorLiteral(term: BitVectorLiteral): T
    def visitIfThenElse(term: IfThenElse): T
    def visitClosure(term: Closure): T
    def visitReflexiveClosure(term: ReflexiveClosure): T
}
