package fortress.tfol

import scala.collection.JavaConverters._
import scala.collection.immutable.Seq // Use immutable seq by default

trait TypeCheckQuerying {
    def hasType(sort: Type): Boolean
    def hasTypeWithName(name: String): Boolean
    def hasFunctionWithName(name: String): Boolean
    def queryFunction(name: String, argTypes: Seq[Type]): Option[FuncDecl]
    def queryConstant(v: Var): Option[AnnotatedVar]
    def queryEnum(v: Var): Option[AnnotatedVar]
    def queryUninterpretedFunction(name: String): Option[FuncDecl]
    
    def queryFunctionJava(name: String, argTypes: java.util.List[Type]): java.util.Optional[FuncDecl] =
        queryFunction(name, argTypes.asScala.toList) match {
            case Some(fdecl) => java.util.Optional.of[FuncDecl](fdecl)
            case None => java.util.Optional.empty[FuncDecl]()
        }
        
    def queryConstantJava(v: Var): java.util.Optional[AnnotatedVar] =
        queryConstant(v) match {
            case Some(av: AnnotatedVar) => java.util.Optional.of(av)
            case None => java.util.Optional.empty[AnnotatedVar]
        }
        
    def queryEnumJava(v: Var): java.util.Optional[AnnotatedVar] =
        queryEnum(v) match {
            case Some(av: AnnotatedVar) => java.util.Optional.of(av)
            case None => java.util.Optional.empty[AnnotatedVar]
        }
    
    def queryUninterpretedFunctionJava(name: String): java.util.Optional[FuncDecl] =
        queryUninterpretedFunction(name) match {
            case Some(fdecl) => java.util.Optional.of[FuncDecl](fdecl)
            case None => java.util.Optional.empty[FuncDecl]()
        }
}

trait ExtensibleTypeChecking extends TypeCheckQuerying {
    
}
