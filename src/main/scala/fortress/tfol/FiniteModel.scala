package fortress.tfol

abstract class FiniteModel {
    def constantMappings: Map[AnnotatedVar, DomainElement]
    def functionMappings: Map[FuncDecl, Map[List[DomainElement], DomainElement]]
}
