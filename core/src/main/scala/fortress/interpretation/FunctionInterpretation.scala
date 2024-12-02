package fortress.interpretation

import fortress.msfol._
import fortress.util.Errors
import fortress.util.SmartEq
import fortress.sortinference.SortSubstitution

/**
  * Represents a solved interpretation of a function declaration
  */
trait FunctionInterpretation {
    /**
      * Given arguments, return the resulting value. Exception if not found
      *
      * @return
      */
    def apply(args: Seq[Value]): Value = {
        get(args) match {
            case None => Errors.Internal.impossibleState(f"Failed to get result of ${args} from function interpretation.")
            case Some(x) => x
        }
    }

    /**
      * The resulting value as an option, None if not found
      *
      * @param args
      * @return
      */
    def get(args: Seq[Value]): Option[Value]

    /** 
     * Replaces the Values of an interpretation EnumValues, according to the given substitution map.
     * Useful for undoing Enum Elimination.
     */
    def replaceValuesWithEnums(enumMapping: Map[Value, EnumValue]): FunctionInterpretation

    /**
      * Changes inputs and results based on the sort substitution
      *
      * @param sortSub
      * @return
      */
    def applySortSubstitution(sortSub: SortSubstitution): FunctionInterpretation

    
    /**
      * Generate a set of constraints to defin the output of the function
      *
      * @param fdecl The typed function declaration for this interpretation
      * @return 
      */
    def generateConstraints(fdecl: FuncDecl): Set[Term]


    /**
      * Unapplies the BvToInt transformation for this interpretation.
      *
      * @param uncastArgs A function that when applied to the arguments of the function will unapply the IntToBv transformation on them
      * @param castResult Should the result be cast
      * @param bvToInt Function to cast the result back to an integer
      * @return
      */
    def unapplyIntToBv(uncastArgs: Seq[Value] => Seq[Value], castResult: Boolean, bvToInt: Value => IntegerLiteral): FunctionInterpretation
}



/**
  * A function interpretation that always returns the same value
  *
  * @param value the value the function returns
  */
class ConstantFunctionInterpretation(value: Value) extends FunctionInterpretation {
    override def get(args: Seq[Value]) = Some(value)

    def getValue(): Value = value

    override def replaceValuesWithEnums(enumMapping: Map[Value, EnumValue]): FunctionInterpretation = {
        if (enumMapping contains value) {
            new ConstantFunctionInterpretation(enumMapping(value))
        } else {
            this
        }
    }

    override def applySortSubstitution(sortSub: SortSubstitution): FunctionInterpretation = {
        return new ConstantFunctionInterpretation(sortSub.applyValueKeepInts(value))
    }

    override def generateConstraints(fdecl: FuncDecl): Set[Term] = {
        val prefix = (if (fdecl.name.startsWith("arg")) "param" else "arg")

        val sorts = fdecl.argSorts
        // raw arguments
        val args = Range(0, sorts.length) map (n => Var(prefix + n.toString()))

        // Annotated arguments
        val annotatedArgs = sorts.zip(args).map({case (sort, arg) => AnnotatedVar(arg, sort)})

        val term = Forall(annotatedArgs, SmartEq.smartEq(fdecl.resultSort, App(fdecl.name, args.toSeq), value))

        Set(term)
    }

    override def unapplyIntToBv(uncastArgs: Seq[Value] => Seq[Value], castResult: Boolean, bvToInt: Value => IntegerLiteral): FunctionInterpretation = {
        // Only have to cast the result as arguments are ignored
        if (!castResult){
            return this
        }

        val newResult = bvToInt(value)

        return new ConstantFunctionInterpretation(newResult)
    }

}

/**
  * A function interpretation that keeps a mapping from arguments to result values.
  *
  * @param mapping mapping of an argument sequence to a result value
  */
class MapFunctionInterpretation(mapping: Map[Seq[Value], Value]) extends FunctionInterpretation {
    override def get(args: Seq[Value]) = mapping get args

    override def replaceValuesWithEnums(enumMapping: Map[Value,EnumValue]): FunctionInterpretation = {
        // Function to replace values only if they are in the enumMapping
        def replaceWithEnum(v: Value): Value = enumMapping.getOrElse(v, v)

        val newMapping = mapping.map({
            case (args, result) => (
                args.map(replaceWithEnum),
                replaceWithEnum(result)
            )
        })

        new MapFunctionInterpretation(newMapping)

    }

    def applySortSubstitution(sortSub: SortSubstitution): FunctionInterpretation = {
        val newMap: Map[Seq[Value], Value] = mapping map {
            case(args, value) => (args map sortSub.applyValueKeepInts) -> sortSub.applyValueKeepInts(value)
        }
        return new MapFunctionInterpretation(newMap)
    }

    override def generateConstraints(fdecl: FuncDecl): Set[Term] = {
        val name = fdecl.name
        val sort = fdecl.resultSort

        mapping.map({case (args, result) =>
            SmartEq.smartEq(sort, App(name, args), result)
        }).toSet
    }

    override def unapplyIntToBv(uncastArgs: Seq[Value] => Seq[Value], castResult: Boolean, bvToInt: Value => IntegerLiteral): FunctionInterpretation = {
        // Only have to cast the result sometimes
        val newMap = if (castResult){
            mapping.map({
                case (args, result) => (uncastArgs(args), bvToInt(result))
            })
        } else {
            mapping.map({
                case (args, result) => (uncastArgs(args), result)
            })
        }

        return new MapFunctionInterpretation(newMap)
    }
}

/**
  * A function `MapFunctionInterpretation` with a default value.
  *
  * @param mapping mapping of an argument sequence to a result value
  * @param default the value the function returns if the input arguments are not mapped to a specific output
  */
class MapDefaultFunctionInterpretation(mapping: Map[Seq[Value], Value], default: Value) extends FunctionInterpretation {
    // We don't use Scala's withDefault, as it has some inconsistencies between `get` and `apply`
    override def get(args: Seq[Value]) = Some(mapping.getOrElse(args, default))

    override def replaceValuesWithEnums(enumMapping: Map[Value,EnumValue]): FunctionInterpretation = {
        // Function to replace values only if they are in the enumMapping
        def replaceWithEnum(v: Value): Value = enumMapping.getOrElse(v, v)

        val newMapping = mapping.map({
            case (args, result) => (
                args.map(replaceWithEnum),
                replaceWithEnum(result)
            )
        })

        val newDefault = replaceWithEnum(default)

        new MapDefaultFunctionInterpretation(newMapping, newDefault)

    }

    def applySortSubstitution(sortSub: SortSubstitution): FunctionInterpretation = {
        val newMap: Map[Seq[Value], Value] = mapping map {
            case(args, value) => (args map sortSub.applyValueKeepInts) -> sortSub.applyValueKeepInts(value)
        }
        val newDefault = sortSub.applyValueKeepInts(default)
        return new MapDefaultFunctionInterpretation(newMap, newDefault)
    }

    override def generateConstraints(fdecl: FuncDecl): Set[Term] = {
        val prefix = (if (fdecl.name.startsWith("arg")) "param" else "arg")

        val sorts = fdecl.argSorts
        // raw arguments
        val args = Range(0, sorts.length) map (n => Var(prefix + n.toString()))

        // Annotated arguments
        val annotatedArgs = sorts.zip(args).map({case (sort, arg) => AnnotatedVar(arg, sort)})


        // Forall args. args = an input and we get the corresponding result or it is not equal to any of these and we get the default
        val matchesMapping = mapping.map({case (args, result) =>
            SmartEq.smartEq(fdecl.resultSort, App(fdecl.name, args), result)
        }).toSet
        
        // The arguments match no mapping
        val matchesNoMapping = Not(Or.smart(
            mapping.keys.map(argValues =>
                // And each arg = the matching value
                And.smart(annotatedArgs.zip(argValues).map({
                    case (AnnotatedVar(paramVar, sort), argValue) => SmartEq.smartEq(sort, paramVar, argValue)
                }).toSeq)
            ).toSeq
        ))

        val takeDefault = Forall(annotatedArgs,
                Implication(matchesNoMapping, SmartEq.smartEq(fdecl.resultSort, App(fdecl.name, args), default))
        )
                
        // Either we get the value from a match or we take the default value
        matchesMapping + takeDefault
    }

    override def unapplyIntToBv(uncastArgs: Seq[Value] => Seq[Value], castResult: Boolean, bvToInt: Value => IntegerLiteral): FunctionInterpretation = {
        // Only have to cast the result sometimes
        val newMap = if (castResult){
            mapping.map({
                case (args, result) => (uncastArgs(args), bvToInt(result))
            })
        } else {
            mapping.map({
                case (args, result) => (uncastArgs(args), result)
            })
        }

        val newDefault = if (castResult) {
            bvToInt(default)
        } else {
            default
        }

        return new MapDefaultFunctionInterpretation(newMap, newDefault)
    }
}