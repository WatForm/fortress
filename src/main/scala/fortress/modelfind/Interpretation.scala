package fortress.modelfind

import fortress.tfol._

trait Interpretation {
    def constantMappings: Map[AnnotatedVar, DomainElement]
    def functionMappings: Map[FuncDecl, Map[List[DomainElement], DomainElement]]
}
