package fortress.operations

import fortress.msfol._
import fortress.util.Errors
import fortress.data.NameGenerator
import fortress.interpretation.Interpretation
import fortress.sortinference.SortSubstitution
import fortress.sortinference.ValuedSortSubstitution
import fortress.problemstate.ProblemState

class IntegerToSortConverter(min: Int, max: Int, newSort: Sort, nameGenerator: NameGenerator) {
    val intToConstants: Map[Int, DomainElement] = Range(min, max+1).map(value => {
        // Domain elements are indexed starting with 1
        (value -> DomainElement(1 - min + value, newSort))
    }).toMap

    val IntConsts = Seq(intToConstants.values)

    val constantsToInts: Map[Value, IntegerLiteral] = intToConstants.map(mapping => mapping._2 -> IntegerLiteral(mapping._1))

    // TODO name generator
    // If any 
    var convertedFunctions: scala.collection.mutable.Map[BuiltinFunction, FunctionDefinition] = scala.collection.mutable.Map()

    private val x = Var("x")
    private val y = Var("y")
    private val z = Var("z")
    private val ax = x.of(newSort)
    private val ay = y.of(newSort)
    private val az = z.of(newSort)
    private val axy = Seq(ax, ay)
    private val axyz = Seq(ax, ay, az)

    var castToInt: FunctionDefinition = FunctionDefinition(nameGenerator.freshName(f"cast${newSort.name}ToInt"), Seq(ax), IntSort,
        // Generate the body by folding to make If(x == v1) then {1} else {If (x == v2) then {2} else {...  else {<any dummy value>}}}
        constantsToInts.foldLeft(IntegerLiteral(min): Term)({case (prev, (constValue, intValue)) => IfThenElse(Eq(x, constValue), intValue, prev)})
    )

    var castFromInt: FunctionDefinition = FunctionDefinition(nameGenerator.freshName(f"castIntTo${newSort.name}"), Seq(ax), newSort,
        intToConstants.foldLeft(intToConstants(min): Term)({ case (prev, (intValue, constValue)) => IfThenElse(Eq(x, IntegerLiteral(intValue)), constValue, prev)})
    )

    private def inRange(x: Int): Boolean = {
        return (x >= min && x <= max)
    }

    // wraps a term in a fromInt cast. Simplifies out toInts
    def fromInt(arg: Term): Term = arg match {
        case App(fname, inner) if fname == castToInt.name && inner.size == 1 => inner(0)
        case _ => App(castFromInt.name, arg)
    }

    // wraps a term in a toInt cast. Simplifies out fromInts
    def toInt(arg: Term): Term = arg match {
        case App(fname, inner) if fname == castFromInt.name && inner.size == 1 => inner(0)
        case _ => App(castToInt.name, arg)
    }

    // TODO apply to problem state


    def replaceSort(s: Sort): Sort = s match {
        case IntSort => newSort
        case _ => s
    }

    // Change the sort of annotated vars of sort int to the newSort. other sorts are unchanged
    def replaceAvarSort(av: AnnotatedVar): AnnotatedVar = av.sort match {
        case IntSort => AnnotatedVar(av.variable, newSort)
        case _ => av
    }

    def castArgsForUninterpreted(args: Seq[Term], paramSorts: Seq[Sort]): Seq[Term] = {
        args.zip(paramSorts).map({case (arg, sort) => sort match {
            case `newSort` => fromInt(arg)
            case _ => arg
        }})
    }

    def convertSignature(originalSig: Signature): Signature = {
        val sorts = originalSig.sorts + newSort
        val castConstDecls = originalSig.constantDeclarations.map(replaceAvarSort)
        // Constant definitions shouldn't need to be cast
        // Not 100% sure though, so if you're looking for bugs check here.
        val castFuncDecls = originalSig.functionDeclarations.map({case FuncDecl(fname, paramSorts, resultSort) =>
                val newParamSorts = paramSorts map replaceSort
                val newResultSort = replaceSort(resultSort)
                FuncDecl(fname, newParamSorts, newResultSort)
            })
        
        // We don't add overflow checks for definitions here, though maybe we should?
        Signature(
            sorts,
            castFuncDecls,
            originalSig.functionDefinitions,
            castConstDecls,
            originalSig.constantDefinitions,
            originalSig.enumConstants,
        )
    }


    def replaceInt(term: Term, sig: Signature): Term = term match {
        // Quantifiers: replace Int sorts with newSort and recurse
        case Forall(vars, body) => {
            val newVars = vars map replaceAvarSort
            val newSig = sig.withConstantDeclarations(newVars)
            Forall(newVars, replaceInt(body, newSig))
        }
        case Exists(vars, body) => {
            val newVars = vars map replaceAvarSort
            val newSig = sig.withConstantDeclarations(newVars)
            Exists(newVars, replaceInt(body, newSig))
        }

        case App(fname, args) => {
            val recursedArgs = args.map(replaceInt(_, sig))
            sig.queryFunction(fname) match {
                // Cast int args to 
                case None => Errors.Internal.preconditionFailed(f"No function with name ${fname} in signature")
                case Some(Left(FuncDecl(_, paramSorts, resultSort))) => {
                    // Cast if parameter sort is the new sort
                    val castArgs = castArgsForUninterpreted(recursedArgs, paramSorts)
                    
                    val appWithCastArgs = App(fname, castArgs)

                    if (resultSort == newSort) {
                        toInt(appWithCastArgs)
                    } else {
                        appWithCastArgs
                    }
                }
                // Just recurse, don't cast
                case Some(Right(FunctionDefinition(_, params, resultSort, _))) => {
                    App(fname, recursedArgs)
                }
            }
        }

        // Closure arguments to uninterpreted functions must be cast like normal calls
        // We don't have to check result sort here
        case Closure(functionName, arg1, arg2, fixedArgs) => {
            val args = arg1 +: arg2 +: fixedArgs
            val recursedArgs = args.map(replaceInt(_, sig))
            sig.queryFunction(functionName) match {
                case None => Errors.Internal.preconditionFailed(f"Cannot find sort for function |${functionName}|")
                case Some(Right(_)) => Closure(functionName, recursedArgs(0), recursedArgs(1), recursedArgs.tail.tail)
                case Some(Left(FuncDecl(_, paramSorts, _))) => {
                    val castArgs = castArgsForUninterpreted(recursedArgs, paramSorts)
                    Closure(functionName, castArgs(0), castArgs(1), castArgs.tail.tail)
                }
            }
        }

        case ReflexiveClosure(functionName, arg1, arg2, fixedArgs) => {
            val args = arg1 +: arg2 +: fixedArgs
            val recursedArgs = args.map(replaceInt(_, sig))
            sig.queryFunction(functionName) match {
                case None => Errors.Internal.preconditionFailed(f"Cannot find sort for function |${functionName}|")
                case Some(Right(_)) => ReflexiveClosure(functionName, recursedArgs(0), recursedArgs(1), recursedArgs.tail.tail)
                case Some(Left(FuncDecl(_, paramSorts, _))) => {
                    val castArgs = castArgsForUninterpreted(recursedArgs, paramSorts)
                    ReflexiveClosure(functionName, castArgs(0), castArgs(1), castArgs.tail.tail)
                }
            }
        }

        // Cast to int if this is newSort. Otherwise leave unchanged.
        case v: Var => {
            sig.queryConstantDeclaration(v) match {
                case None => Errors.Internal.preconditionFailed(f"IntegerToSort can't find sort of variable ${v.name}")
                case Some(sort) => sort match {
                    case `newSort` => toInt(v)
                    case _ => term
                }
            }
        }

        // Pass recursion through
        case AndList(arguments) => AndList(arguments.map(replaceInt(_, sig)))
        case OrList(arguments) => OrList(arguments.map(replaceInt(_, sig)))
        case BuiltinApp(function, arguments) => BuiltinApp(function, arguments.map(replaceInt(_, sig)))
        case Distinct(arguments) => Distinct(arguments.map(replaceInt(_, sig)))
        case Eq(left, right) => Eq(replaceInt(left, sig), replaceInt(right, sig))
        case Iff(left, right) => Iff(replaceInt(left, sig), replaceInt(right, sig))
        case Implication(left, right) => Implication(replaceInt(left, sig), replaceInt(right, sig))
        case Not(body) => Not(replaceInt(body, sig))
        case IfThenElse(c, t, f) => {
            IfThenElse(replaceInt(c, sig), replaceInt(t, sig), replaceInt(f, sig))
        }

        // Other leaf terms are unchanged
        case _: LeafTerm => term

        // Should be gone by now
        case _: Exists2ndOrder => Errors.Internal.impossibleState("IntegerToSortConverter does not support 2nd order functions.")
        case _: Forall2ndOrder => Errors.Internal.impossibleState("IntegerToSortConverter does not support 2nd order functions.")
    }

    def unapplyInterp(): Interpretation => Interpretation = {
        val sortSub: SortSubstitution = new ValuedSortSubstitution(
            Map(newSort -> IntSort),
            constantsToInts
        )
        def unapply(interp: Interpretation): Interpretation = {
            interp.withoutFunctionDefinitions(
                Set(castToInt, castFromInt)
            ).applySortSubstitution(sortSub)
        }
        return unapply
    }

    def transformProblemState(ps: ProblemState): ProblemState = {
        val newSig = convertSignature(ps.theory.signature)
        val newAxioms = ps.theory.axioms.map(replaceInt(_, newSig))
        val newTheory = Theory(newSig, newAxioms)
        ps.withTheory(newTheory).addUnapplyInterp(unapplyInterp())
    }

    def overflows(): PartialFunction[Term, (Term, Term)] = {
    case App(fname, args) if fname == castToInt.name => {
        Errors.Internal.precondition(args.size == 1, f"Expected only 1 argument to ${castToInt.name}, got ${args.size}")
        val arg = args(0)
        val check = Or(
            BuiltinApp(IntGT, arg, IntegerLiteral(max)),
            BuiltinApp(IntLT, arg, IntegerLiteral(min))
        )
        (App(fname, args), check)
    }}
}