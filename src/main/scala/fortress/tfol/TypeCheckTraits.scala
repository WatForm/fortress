package fortress.tfol

import scala.collection.JavaConverters._
import scala.collection.immutable.Seq // Use immutable seq by default
import fortress.util.Errors

trait TypeCheckQuerying {
    def hasSort(sort: Sort): Boolean
    def hasSortWithName(name: String): Boolean
    def hasFunctionWithName(name: String): Boolean
    def queryFunction(name: String, argSorts: Seq[Sort]): Option[FuncDecl]
    def queryConstant(v: Var): Option[AnnotatedVar]
    def queryEnum(e: EnumValue): Option[Sort]
    def queryUninterpretedFunction(name: String): Option[FuncDecl]
    
    def queryFunctionJava(name: String, argSorts: java.util.List[Sort]): java.util.Optional[FuncDecl] =
        queryFunction(name, argSorts.asScala.toList) match {
            case Some(fdecl) => java.util.Optional.of[FuncDecl](fdecl)
            case None => java.util.Optional.empty[FuncDecl]()
        }
        
    def queryConstantJava(v: Var): java.util.Optional[AnnotatedVar] =
        queryConstant(v) match {
            case Some(av) => java.util.Optional.of(av)
            case None => java.util.Optional.empty[AnnotatedVar]
        }
        
    def queryEnumJava(e: EnumValue): java.util.Optional[Sort] =
        queryEnum(e) match {
            case Some(t) => java.util.Optional.of(t)
            case None => java.util.Optional.empty[Sort]
        }
    
    def queryUninterpretedFunctionJava(name: String): java.util.Optional[FuncDecl] =
        queryUninterpretedFunction(name) match {
            case Some(fdecl) => java.util.Optional.of[FuncDecl](fdecl)
            case None => java.util.Optional.empty[FuncDecl]()
        }
}

trait ExtensibleTypeChecking extends TypeCheckQuerying {
    def extensions: Set[SignatureExtension]
    
    def hasSortBase(sort: Sort): Boolean
    def hasSortWithNameBase(name: String): Boolean
    def hasFunctionWithNameBase(name: String): Boolean
    def queryFunctionBase(name: String, argSorts: Seq[Sort]): Option[FuncDecl]
    def queryConstantBase(v: Var): Option[AnnotatedVar]
    def queryEnumBase(e: EnumValue): Option[Sort]
    def queryUninterpretedFunctionBase(name: String): Option[FuncDecl]
    
    override def hasSort(sort: Sort): Boolean =
        extensions.exists(_.hasSort(sort)) || hasSortBase(sort)
    
    override def hasSortWithName(name: String): Boolean =
        extensions.exists(_.hasSortWithName(name)) || hasSortWithNameBase(name)
    
    override def hasFunctionWithName(name: String): Boolean =
        extensions.exists(_.hasFunctionWithName(name)) || hasFunctionWithNameBase(name)
    
    override def queryFunction(name: String, argSorts: Seq[Sort]): Option[FuncDecl] = {
        val matches: Set[FuncDecl] = extensions.flatMap(extension => extension.queryFunction(name, argSorts))
        Errors.assertion(matches.size <= 1, "Found multiple matches to function " + name + ": " + argSorts)
        if(matches.nonEmpty) Some(matches.head)
        else queryFunctionBase(name, argSorts)
    }
    
    override def queryConstant(v: Var): Option[AnnotatedVar] = {
        val matches: Set[AnnotatedVar] = extensions.flatMap(extension => extension.queryConstant(v))
        Errors.assertion(matches.size <= 1, "Found multiple matches for constant " + v.name)
        if(matches.nonEmpty) Some(matches.head)
        else queryConstantBase(v)
    }
    
    override def queryEnum(e: EnumValue): Option[Sort] = {
        val matches: Set[Sort] = extensions.flatMap(extension => extension.queryEnum(e))
        Errors.assertion(matches.size <= 1, "Found multiple matches for enum " + e.name)
        if(matches.nonEmpty) Some(matches.head)
        else queryEnumBase(e)
    }
    
    override def queryUninterpretedFunction(name: String): Option[FuncDecl] = {
        val matches: Set[FuncDecl] = extensions.flatMap(extension => extension.queryUninterpretedFunction(name))
        Errors.assertion(matches.size <= 1, "Found multiple matches for function " + name)
        if(matches.nonEmpty) Some(matches.head)
        else queryUninterpretedFunctionBase(name)
    }
}
