package fortress.msfol 

import fortress.data.InsertionOrderedSet
import fortress.util.Errors
import fortress.operations.TypeCheckResult
import scala.jdk.CollectionConverters._
import scala.annotation.varargs // So we can call Scala varargs methods from Java
import fortress.operations._
import fortress.interpretation.Interpretation
import fortress.interpretation.BasicInterpretation
import fortress.operations.TermOps._

// Persistent and Immutable
// Internally consistent
// The constructor is private -- the only way to make signatures outside of this class
// is through the empty and withXYZ methods

/** Stores the symbols used for the logic.
  *
  * @param sorts the set of sort symbols
  * @param functionDeclarations the set of function symbols
  * @param constants the set of constant symbols
  * @param enumConstants maps sorts to their list of enumeration symbols (sorts which do not use enums do not appear in this map)
  */
case class Signature private (
    sorts: Set[Sort],
    functionDeclarations: Set[FuncDecl],
    functionDefinitions: Set[FunctionDefinition],
    constantDeclarations: Set[AnnotatedVar],
    constantDefinitions: Set[ConstantDefinition],
    enumConstants: Map[Sort, Seq[EnumValue]]
) {
    
    // TODO need to check this type is not builtin
    def withSort(t: Sort): Signature = {
        if(t.isBuiltin) this
        else {
            assertSortConsistent(t)
            this.copy(sorts=sorts+t)
        }
    }
    
    def withSorts(sorts: java.lang.Iterable[Sort]): Signature = {
        var sig: Signature = this
        sorts.forEach { t =>
            sig = sig.withSort(t)
        }
        sig
    }
    
    @varargs
    def withSorts(sorts: Sort*): Signature = withSorts(sorts.asJava)
    
    def withFunctionDeclaration(fdecl: FuncDecl): Signature = {
        assertFuncDeclConsistent(fdecl)
        this.copy(functionDeclarations= functionDeclarations + fdecl)
    }
    
    def withFunctionDeclarations(fdecls: java.lang.Iterable[FuncDecl]): Signature = {
        var sig: Signature = this
        fdecls.forEach { f =>
            sig = sig.withFunctionDeclaration(f)
        }
        sig
    }
    
    def withFunctionDeclarations(fdecls: Iterable[FuncDecl]): Signature = {
        var sig = this
        fdecls.foreach { f =>
            sig = sig.withFunctionDeclaration(f)
        }
        sig
    }
    
    @varargs
    def withFunctionDeclarations(fdecls: FuncDecl*): Signature = withFunctionDeclarations(fdecls.asJava)
    
    def withConstantDeclaration(c: AnnotatedVar): Signature = {
        assertConstDeclConsistent(c);
        this.copy(constantDeclarations = constantDeclarations + c)
    }
    
    def withConstantDeclarations(constants: java.lang.Iterable[AnnotatedVar]): Signature = {
        var sig = this
        constants.forEach { c =>
            sig = sig.withConstantDeclaration(c)
        }
        sig
    }
    
    def withConstantDeclarations(constants: Iterable[AnnotatedVar]): Signature = {
        var sig = this
        constants.foreach { c =>
            sig = sig.withConstantDeclaration(c)
        }
        sig;
    }
    
    @varargs
    def withConstantDeclarations(constants: AnnotatedVar*): Signature = withConstantDeclarations(constants.asJava)
    
    def withConstantDefinition(cDef: ConstantDefinition): Signature = {
        assertConstantDefnConsistent(cDef)
        this.copy(constantDefinitions = constantDefinitions + cDef)
    }

    def withConstantDefinitions(constants: Iterable[ConstantDefinition]): Signature = {
        var sig = this
        constants.foreach { c =>
            sig = sig.withConstantDefinition(c)
        }
        sig;
    }

    def withConstantDefinitions(constants: java.lang.Iterable[ConstantDefinition]): Signature = {
        withConstantDefinitions(constants.asScala)
    }

    def withoutConstantDefinitions(): Signature = copy(constantDefinitions = Set.empty)

    def withoutConstantDefinition(cDef: ConstantDefinition): Signature = {
        copy(constantDefinitions = constantDefinitions - cDef)
    }

    def withoutFunctionDefinitions(): Signature = copy(functionDefinitions = Set.empty)

    def withEnumSort(t: Sort, values: Seq[EnumValue]) = {
        // TODO more consistency checking
        this.copy(sorts = sorts+t, enumConstants = enumConstants + (t -> values))    
    }
    
    def withEnumSort(t: Sort, values: java.util.List[EnumValue]) = {
        // TODO more consistency checking
        this.copy(sorts = sorts+t, enumConstants = enumConstants + (t -> values.asScala.toList))
    }

    def withFunctionDefinition(funcDef: FunctionDefinition): Signature = {
        assertFuncDefConsistent(funcDef)
        copy(functionDefinitions = functionDefinitions + funcDef)
    }

    def withFunctionDefinitions(funcdefs: java.lang.Iterable[FunctionDefinition]): Signature = {
        var sig: Signature = this
        funcdefs.forEach { f =>
            sig = sig.withFunctionDefinition(f)
        }
        sig
    }

    def withFunctionDefinitions(funcDefs: Iterable[FunctionDefinition]): Signature = {
        var sig = this
        funcDefs.foreach { f =>
            sig = sig.withFunctionDefinition(f)
        }
        sig
    }

    @varargs
    def withFunctionDefinitions(funcDefs: FunctionDefinition*): Signature = withFunctionDefinitions(funcDefs.asJava)

    def withoutFunctionDefinition(funcDef: FunctionDefinition): Signature = {
        copy(functionDefinitions = functionDefinitions - funcDef)
    }

    def withoutFunctionDefinition(name: String): Signature = {
        copy(functionDefinitions = functionDefinitions.filterNot(_.name == name))
    }

    def withoutFunctionDefinitions(funcDefs: java.lang.Iterable[FunctionDefinition]): Signature = {
        var sig: Signature = this
        funcDefs.forEach( f => {
            sig = sig.withoutFunctionDefinition(f)
        })
        sig
    }

    def withoutFunctionDefinitions(funcDefs: Iterable[FunctionDefinition]): Signature = {
        var sig: Signature = this
        funcDefs.foreach( f => {
            sig = sig.withoutFunctionDefinition(f)
        })
        sig
    }

    def withoutFunctionDefinitions(funcDefs: FunctionDefinition*): Signature = withoutFunctionDefinitions(funcDefs.asJava)

    // TypeChecking
    
    def queryConstantDeclaration(v: Var): Option[AnnotatedVar] = constantDeclarations.find(_.variable == v)

    def queryConstantDefinition(v: Var): Option[ConstantDefinition] = constantDefinitions.find(_.variable == v)

    def queryConstant(v: Var): Option[Either[AnnotatedVar, ConstantDefinition]] = queryConstantDeclaration(v) match {
        case Some(avar) => Some(Left(avar))
        case None => queryConstantDefinition(v) match {
            case Some(cDef) => Some(Right(cDef))
            case None => None
        }
    }

    def getAnnotatedVarOfConstant(v: Var): Option[AnnotatedVar] = queryConstant(v) match {
        case Some(Left(cDecl)) => Some(cDecl)
        case Some(Right(cDefn)) => Some(cDefn.avar)
        case None => None
    }
    
    def queryEnum(e: EnumValue): Option[Sort] = enumConstants.find {
        case (sort, enumConstants) => enumConstants contains e
    }.map { case (sort, _) => sort }
    
    def queryFunctionDeclaration(name: String, argSorts: Seq[Sort]): Option[FuncDecl] =
        functionDeclarations.find(fdecl => fdecl.name == name && fdecl.argSorts == argSorts)
    
    def queryFunctionDeclaration(name: String, argSorts: Seq[Sort], resultSort: Sort): Option[FuncDecl] =
        functionDeclarations.find(_ == FuncDecl(name, argSorts, resultSort))
    
    def queryFunctionDeclaration(name: String): Option[FuncDecl] =
        functionDeclarations.find(fdecl => fdecl.name == name)
    
    def queryFunctionDefinition(name: String, argSorts: Seq[Sort]): Option[FunctionDefinition] = {
        functionDefinitions.find(fdefn => fdefn.name == name && fdefn.argSorts == argSorts)
    }

    def queryFunctionDefinition(name: String): Option[FunctionDefinition] = {
        functionDefinitions.find(_.name == name)
    }
    
    def queryFunction(name: String): Option[Either[FuncDecl, FunctionDefinition]] = {
        queryFunctionDeclaration(name) match {
            case Some(decl) => Some(Left(decl))
            case None => functionDefinitions.find(_.name == name) match {
                case Some(defn) => Some(Right(defn))
                case None => None
            }
        }
    }

    def queryFunction(name: String, argSorts: Seq[Sort]): Option[Either[FuncDecl, FunctionDefinition]] = {
        queryFunctionDeclaration(name, argSorts) match {
            case Some(decl) => Some(Left(decl))
            case None => queryFunctionDefinition(name, argSorts) match {
                case Some(defn) => Some(Right(defn))
                case None => None
            }
        }
    }

    def definitionsInDependencyOrder(): Seq[Either[ConstantDefinition, FunctionDefinition]] = {
        var sorted: Seq[Either[ConstantDefinition, FunctionDefinition]] = Seq.empty
        // We only care about dependencies to other definitions
        val possibleDependences = constantDefinitions.map(_.name) union functionDefinitions.map(_.name)
        // Get the dependencies
        val constDependencies = constantDefinitions.map(cDef =>{
            val dependencies = possibleDependences intersect RecursiveAccumulator.constantsAndFunctionsIn(cDef.body)
            (Left(cDef), dependencies)
        })
        val funcDependencies = functionDefinitions.map(fDef => {
            val argNames = fDef.argSortedVar.map(_.name)
            val dependencies = (possibleDependences -- argNames) intersect RecursiveAccumulator.constantsAndFunctionsIn(fDef.body)
            (Right(fDef), dependencies)
        })
        var remaining = constDependencies ++ funcDependencies

        while(!remaining.isEmpty){
            // Check which no longer have dependencies
            val (readyEntries, dependentEntries) = remaining.partition(_._2.isEmpty)

            val readyDefinitions = readyEntries.map(_._1) // Get just the definition
            sorted = sorted ++ readyDefinitions.toSeq

            val readyNames = readyDefinitions.map(_.fold(_.name, _.name))

            // The remaining is the dependent entries without the printed dependencies
            remaining = dependentEntries.map({
                case (defn, deps) => (defn, deps diff readyNames)
            })

        }

        sorted
    }
    
    def hasSort(sort: Sort): Boolean = sorts contains sort
    
    def hasSortWithName(name: String): Boolean = sorts.exists(_.name == name)
    
    def hasFuncDeclWithName(name: String): Boolean = functionDeclarations.exists(_.name == name)

    def hasFuncDefWithName(name: String): Boolean = functionDefinitions.exists(_.name == name)
    
    def functionWithName(name: String): Option[FuncDecl] = functionDeclarations.find(_.name == name)
    
    // Includes an unapply function
    def replaceIntegersWithBitVectors(bitwidth: Int): (Signature, Interpretation => Interpretation) = {
        def replaceSort(s: Sort): Sort = s match {
            case IntSort => BitVectorSort(bitwidth)
            case _ => s
        }

        def replaceSortInAnnVar(v: AnnotatedVar): AnnotatedVar = {
            if(v.sort == IntSort){
                AnnotatedVar(v.variable, BitVectorSort(bitwidth))
            }
            else v
        }
        
        val newSorts = sorts

        var replacedFunctionDeclarations: Map[FuncDecl, FuncDecl] = Map.empty
        val newFunctionDeclarations = functionDeclarations.map(
            fdecl => {
                val newFdecl = FuncDecl(fdecl.name, fdecl.argSorts map replaceSort, replaceSort(fdecl.resultSort))
                if (fdecl != newFdecl){
                    replacedFunctionDeclarations = replacedFunctionDeclarations + (newFdecl -> fdecl)
                }
                newFdecl
            }
        )
        
        // Function definitions will not reappear. No need to save
        //var replacedFunctionDefinitions: Map[FunctionDefinition, FunctionDefinition] = Map.empty
        val newFunctionDefinitions = functionDefinitions.map(
            //Something in this seems wrong. What about integer args?
            funcDef => {
                if( funcDef.resultSort == UnBoundedIntSort ) funcDef
                else {
                    val newDef = FunctionDefinition(
                        funcDef.name,
                        funcDef.argSortedVar.map(replaceSortInAnnVar),
                        replaceSort(funcDef.resultSort),
                        TermConverter.intToSignedBitVector(funcDef.body, bitwidth)
                    )
                    newDef
                }
                
            }
        )

        val newConstantDefinitions: Set[ConstantDefinition] = constantDefinitions.map(cDef => {
            val newDef = ConstantDefinition(replaceSortInAnnVar(cDef.avar), TermConverter.intToSignedBitVector(cDef.body, bitwidth))
            newDef
        })


        var replacedConstantDeclarations: Map[AnnotatedVar, AnnotatedVar] = Map.empty

        val newConstantDeclarations = constantDeclarations.map(c => {
            val newDecl = c.variable of replaceSort(c.sort)
            if (c != newDecl){
                replacedConstantDeclarations = replacedConstantDeclarations + (newDecl -> c)
            }
            newDecl
        })
        val newEnums = enumConstants

        def bvToInt(value: Value): IntegerLiteral = value match {
            case BitVectorLiteral(value, bitwidth) => {
                // If the value here is incorrect we will change it
                val maxPlusOne = Math.pow(2, bitwidth-1);
                if (value >= maxPlusOne){
                    Errors.Internal.impossibleState(f"Bitvectror ${value} is unsigned in BVUNAPPLY.")
                }
                IntegerLiteral(value)
            }
            case _ => Errors.Internal.impossibleState("Trying to cast nonbitvector value '"+ value.toString()+"' to an integer.")
        }
        def unapply(interp: Interpretation): Interpretation = {
            // There's only one kind of interpretation
            // This is an ugly workaround
            var newInterp = interp match {
                case x: BasicInterpretation => x
            }
            // constants we translated get converted to integers
            val newConsts = interp.constantInterpretations
                .map({case (avar, value) =>
                    if (replacedConstantDeclarations.isDefinedAt(avar)){
                        (replacedConstantDeclarations(avar), bvToInt(value))
                    } else {
                        (avar, value)
                    }
            })

            // We cast definitions back as needed



            val newFunctionDefinitions = interp.functionDefinitions
                .map(fDef => {
                    
                    val decOfDef = FuncDecl(fDef.name, fDef.argSorts, fDef.resultSort)
                    if (replacedFunctionDeclarations.isDefinedAt(decOfDef)){
                        // cast the args properly
                        val originalDec: FuncDecl = replacedFunctionDeclarations(decOfDef)

                        // Change the sorts of the arguments back to what they should have been
                        val newArgSorts = (originalDec.argSorts zip fDef.argSortedVar).map(_ match{
                            case (origSort, AnnotatedVar(varName, _)) => varName of origSort
                        })

                        // New definition, we will make casts in the body to allow the casted args and output to still be used
                        var newDef = FunctionDefinition(fDef.name, newArgSorts, originalDec.resultSort, fDef.body)

                        // Cast each int arg to a bitvector in the body
                        val substitutionsToMake = (originalDec.argSorts zip fDef.argSortedVar)
                            .filter(pair => pair._1 != pair._2.sort)
                            .map(pair => (pair._2.variable, BuiltinApp(CastIntToBV(bitwidth), pair._2.variable)))
                            .toMap
                        newDef = newDef.copy(body = newDef.body.fastSubstitute(substitutionsToMake))

                        // If we would have outbut a bitvector, and should output int, cast the body back
                        (originalDec.resultSort, fDef.resultSort) match {
                            case (IntSort, BitVectorSort(_)) => {
                                newDef = newDef.copy(body = BuiltinApp(CastBVToInt, newDef.body))
                            }
                            case _ => ()
                        }
                        
                        newDef
                    } else {
                        fDef
                    }
                })
            
            val newFunctionInterps: Map[FuncDecl, Map[Seq[Value], Value]] = interp.functionInterpretations
                .map({
                    case (fDec, valueMap) if replacedFunctionDeclarations.isDefinedAt(fDec) => {
                        val newDec = replacedFunctionDeclarations(fDec)

                        // find indices of args that were cast
                        val differentIndices: Seq[Int] = for {
                            i <- newDec.argSorts.indices
                            if newDec.argSorts(i) != fDec.argSorts(i)
                        } yield i
                        // replace args that got cast
                        def uncastArgs(args: Seq[Value]): Seq[Value] = {
                            var newArgs = args
                            for (i <- differentIndices){
                                newArgs = newArgs.updated(i, bvToInt(newArgs(i)))
                            }
                            newArgs
                        }
                        val newValueMap = valueMap.map({
                            case (args, result) => (uncastArgs(args), bvToInt(result))
                        })
                        (newDec, newValueMap)
                    }
                    case x => x
                })


            BasicInterpretation(
                interp.sortInterpretations,
                newConsts,
                newFunctionInterps,
                newFunctionDefinitions)
        }


        val newSig = Signature(newSorts, newFunctionDeclarations, newFunctionDefinitions, newConstantDeclarations, newConstantDefinitions, newEnums)
        (newSig, unapply)
    }

    def replaceIntSorts(boundedSet: Set[String]): Signature = {
        def replace(s: Sort): Sort = s match {
            case IntSort => UnBoundedIntSort
            case _ => s
        }

        def replaceAnnVar(v: AnnotatedVar): AnnotatedVar = {
            if( v.sort == IntSort ) AnnotatedVar(v.variable, UnBoundedIntSort)
            else v
        }

        val newSorts = sorts
        val newFunctionDeclarations = functionDeclarations.map(funcDecl => {
            if( !boundedSet.contains(funcDecl.name) ) {
                FuncDecl(funcDecl.name, funcDecl.argSorts map replace, replace(funcDecl.resultSort))
            }
            else{
                funcDecl
            }
        })

        val newFunctionDefinitions = functionDefinitions.map(funcDef => {
            if(!boundedSet.contains(funcDef.name)) {
                FunctionDefinition(funcDef.name, funcDef.argSortedVar.map(replaceAnnVar), replace(funcDef.resultSort), funcDef.body)
            }
            else funcDef
        })
        val newConstantDeclarations = constantDeclarations.map(const => {
            if(!boundedSet.contains(const.name)) {
                const.variable of replace(const.sort)
            }
            else const
        })
        val newConstantDefinitions = constantDefinitions.map(cDef => {
            if(!boundedSet.contains(cDef.name)){
                cDef.copy(avar = replaceAnnVar(cDef.avar)) // Copying from fdef but I feel like the body might need transforming?
            }
            else cDef
        })
        val newEnums = enumConstants
        Signature(newSorts, newFunctionDeclarations, newFunctionDefinitions, newConstantDeclarations, newConstantDefinitions, newEnums)
    }
    
    def withoutEnums = copy(enumConstants = Map.empty)
    
    private
    def assertSortConsistent(t: Sort): Unit = {
        // Sort must not share a name with any function declaration
        Errors.Internal.precondition(! hasFuncDeclWithName(t.name), "Name " + t.name + " shared by sort and function declaration")

        // Sort must not share a name with any function definition
        Errors.Internal.precondition(! hasFuncDefWithName(t.name), "Name " + t.name + " shared by sort and function definition")

        // Sort must not share a name with any constant
        Errors.Internal.precondition(queryConstant(Var(t.name)).isEmpty, "Name " + t.name + " shared by sort and constant")
    }
    
    private 
    def assertConstDeclConsistent(c: AnnotatedVar): Unit = {
        // Constant's sort must be within the set of sorts
        Errors.Internal.precondition(c.sort.isBuiltin || hasSort(c.sort), "Constant " + c.toString + " of undeclared sort ")
        
        // Constant cannot share a name with a constant definition
        Errors.Internal.precondition(queryConstantDefinition(c.variable).isEmpty, f"Constant ${c.name} declared when it is already defined")

        // Constant cannot share a name with a constant declaration of a different sort
        Errors.Internal.precondition(queryConstantDeclaration(c.variable).filter(_.sort != c.sort).isEmpty, "Constant " + c.name + " declared with two different sorts")
        
        // Constant cannot share a name with any function declaration
        //Errors.Internal.precondition(! hasFuncDeclWithName(c.name), "Name " + c.name + " shared by constant and function declaration")

        // Constant cannot share a name with any function definition
        //Errors.Internal.precondition(! hasFuncDefWithName(c.name), "Name " + c.name + " shared by constant and function definition")

    }

    private def assertConstantDefnConsistent(cDef: ConstantDefinition): Unit = {
        // Constant Definition's sort must be within the set of sorts
        Errors.Internal.precondition(cDef.sort.isBuiltin || hasSort(cDef.sort), f"Constant definition ${cDef} of undeclared sort ${cDef.sort}.")

        // Constant cannot share a name with a constant declaration
        Errors.Internal.precondition(queryConstantDeclaration(cDef.variable).isEmpty, f"Constant ${cDef.name} defined when it is already declared.")

        // Constant cannot share a name with a different constant definition
        Errors.Internal.precondition(queryConstantDefinition(cDef.variable).filter(_ != cDef).isEmpty, f"Constant ${cDef.name} is defined twice.")

        // Constant cannot share a name with any function
        //Errors.Internal.precondition(queryFunction(cDef.name).isEmpty, f"Name ${cDef.name} shared by constant definition and function.")
    }
    
    private
    def assertFuncDeclConsistent(fdecl: FuncDecl): Unit = {
        // Argument sorts must exist in sort set
        Errors.Internal.precondition(fdecl.argSorts.forall(s => s.isBuiltin || hasSort(s)),
            "Function " + fdecl.name + " has argument sorts that are undeclared")
            
        // Result sort must exist in sort set
        Errors.Internal.precondition(fdecl.resultSort.isBuiltin || hasSort(fdecl.resultSort),
            "Function " + fdecl.name + " has result sort that is undeclared")
            
        // Function must not share name with a constant
        //Errors.Internal.precondition(queryConstant(Var(fdecl.name)).isEmpty,
        //    "Name " + fdecl.name +  " shared by function and constant")
        
        // Function must not share name with a sort
        Errors.Internal.precondition(! hasSortWithName(fdecl.name), "Name " + fdecl.name +  " shared by function and sort")

        // function declaration must not share name with another function definition
        // TODO should this be of same arity/typesig?
        Errors.Internal.precondition(
            !hasFuncDefWithName(fdecl.name), "Name " + fdecl.name + " shared by function definition and function declaration"
        )

        // Function must not share name with another function, unless it is the same function
        Errors.Internal.precondition(
            ! hasFuncDeclWithName(fdecl.name) || // No function has same name
            queryFunctionDeclaration(fdecl.name, fdecl.argSorts).filter(_ == fdecl).nonEmpty, // Same function exists
            "Function " + fdecl.name + " declared with two different function declarations")
    }

    private
    def assertFuncDefConsistent(fdef: FunctionDefinition): Unit = {
        // Argument sorts must exist in sort set
        Errors.Internal.precondition(fdef.argSortedVar.forall(arg => arg.sort.isBuiltin || hasSort(arg.sort)),
            "Function " + fdef.name + " has argument sorts that are undeclared")

        // Result sort must exist in sort set
        Errors.Internal.precondition(fdef.resultSort.isBuiltin || hasSort(fdef.resultSort),
            "Function " + fdef.name + " has result sort that is undeclared")

        // Function must not share name with a constant
        //Errors.Internal.precondition(queryConstant(Var(fdef.name)).isEmpty,
        //    "Name " + fdef.name +  " shared by function and constant")

        // Function must not share name with a sort
        Errors.Internal.precondition(! hasSortWithName(fdef.name), "Name " + fdef.name +  " shared by function and sort")

        // function definitions must not share name with another function declaration
        Errors.Internal.precondition(
            !hasFuncDeclWithName(fdef.name), "Name " + fdef.name + " shared by function definition and function declaration"
        )

        // Function must not share name with another function, unless it is the same function
        Errors.Internal.precondition(
            !hasFuncDefWithName(fdef.name) || functionDefinitions.contains(fdef),
            "Function " + fdef.name + " declared with two different function definitions")
    }
    
    override def toString: String = {
        val sortString = "Sorts: " + sorts.mkString(", ")
        
        val enumString = "Enum Sorts:\n" + enumConstants.map {
            case(sort, enumValues) => sort.name + " = {" + enumValues.mkString(", ") + "}"
        }.mkString("\n")
        
        val funcDeclString = "Function declarations:\n" + functionDeclarations.mkString("\n")

        val funcDefString = "Function Definitions:\n" + functionDefinitions.mkString("\n")

        val constDeclString = "Constant Declarations:\n" + constantDeclarations.mkString("\n")

        val constDefnString = "Constant Definitions:\n" + constantDefinitions.mkString("\n")
        
        // Slow but doesn't matter
        var result = "Signature"
        if(sorts.nonEmpty) { result += "\n" + sortString }
        if(enumConstants.nonEmpty) { result += "\n" + enumString }
        if(functionDeclarations.nonEmpty) { result += "\n" + funcDeclString }
        if(functionDefinitions.nonEmpty) { result += "\n" + funcDefString }
        if(constantDeclarations.nonEmpty) { result += "\n" + constDeclString }
        if(constantDefinitions.nonEmpty) {result += "\n" + constDefnString}
        result
    }
}

object Signature {
    def empty: Signature = 
        // For testing consistency for symmetry breaking, use an insertion ordered set
        Signature(InsertionOrderedSet.empty[Sort], InsertionOrderedSet.empty, InsertionOrderedSet.empty, InsertionOrderedSet.empty, InsertionOrderedSet.empty, Map.empty)
}
