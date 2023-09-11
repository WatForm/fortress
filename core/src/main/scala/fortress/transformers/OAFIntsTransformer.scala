package fortress.transformers

import fortress.problemstate.ProblemState
import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.TermOps._
import fortress.operations.RecursiveAccumulator
import fortress.problemstate.ExactScope
import fortress.util.Errors
import fortress.interpretation.Interpretation
import fortress.sortinference._

object OAFIntsTransformer extends ProblemStateTransformer {
    val name: String = "OAFIntsTransformer"

    // Generate mapping using min, max inclusive
    def generateConstantMapping(min: Int, max: Int, sort: Sort): Map[Int, DomainElement] = {
        Range(min, max+1).map(intValue => intValue -> DomainElement(intValue - min + 1, sort)).toMap
    }

    def apply(problemState: ProblemState): ProblemState = {
        // early leave if we don't have a scope for the intsort
        if (!problemState.scopes.isDefinedAt(IntSort)){
            return problemState
        }

        // We don't want to replicate existing functions or variables or constants
        val forbiddenNames: Set[String] = (
            problemState.theory.constantDeclarations.map(_.name) union problemState.theory.functionDeclarations.map(_.name) union
            problemState.theory.functionDefinitions.map(_.name)
        ).toSet
        val varNameGenerator: NameGenerator = new IntSuffixNameGenerator(forbiddenNames, 0)
        // sorts have their own exclusive names
        val sortNames = problemState.theory.signature.sorts.map(_.name)
        val sortNameGenertor = new IntSuffixNameGenerator(sortNames, 0)

        val newSort = SortConst(sortNameGenertor.freshName("OAFInt"))
        

        // vars to write
        val x = Var("x")
        val z = Var("z")
        val y = Var("y")
        val ax = x.of(newSort)
        val ay = y.of(newSort)
        val az = z.of(newSort)
        val axy = Seq(ax, ay)
        val axyz = Seq(ax, ay, az)

        

        val numValues = problemState.scopes(IntSort).size
        val min = (numValues.toFloat / 2.0).ceil.toInt * -1
        val max = (numValues.toFloat / 2.0).floor.toInt - 1

        val newScopes = problemState.scopes + (newSort -> ExactScope(numValues, true))

        val intToConstants: Map[Int, DomainElement] = generateConstantMapping(min, max, newSort)
        val constantsToInts: Map[DomainElement, Int] = intToConstants.map({ case (ival, varVal) => varVal -> ival})
        // generate interpreted functions to do casting
        val castToIntDefn: FunctionDefinition = FunctionDefinition(varNameGenerator.freshName(f"toInt"), Seq(ax), IntSort,
            // Generate the body by folding to make If(x == v1) then {1} else {If (x == v2) then {2} else {...  else {<any dummy value>}}}
            constantsToInts.foldLeft(IntegerLiteral(min): Term)({case (prev, (constValue, intValue)) => IfThenElse(Eq(x, constValue), IntegerLiteral(intValue), prev)})
        )
        val castFromIntDefn: FunctionDefinition = FunctionDefinition(varNameGenerator.freshName(f"fromInt"), Seq(x.of(IntSort)), newSort,
            intToConstants.foldLeft(intToConstants(min): Term)({ case (prev, (intValue, constValue)) => IfThenElse(Eq(x, IntegerLiteral(intValue)), constValue, prev)})
        )

        // TODO could this be improved by checking out of bounds to remove lots of Nots?
        val isInBounds: FunctionDefinition = FunctionDefinition(varNameGenerator.freshName(f"isInBoundsOAF"), Seq(x.of(IntSort)), BoolSort,
            AndList(
                Term.mkGE(x, IntegerLiteral(min)), // x >= MIN
                Term.mkLE(x, IntegerLiteral(max)) // x <= MAX
            )
        )

        // terms setup to clear cast to/from identities
        def castToInt(term: Term): Term = term match {
            case App(castFromIntDefn.name, Seq(baseTerm)) => baseTerm
            case _ => App(castToIntDefn.name, term)
        }
        def castFromInt(term: Term): Term = term match {
            case App(castToIntDefn.name, Seq(baseTerm)) => baseTerm
            case _ => App(castFromIntDefn.name, term)
        }

        // replaces int sort while leaving other sorts unchanged
        def replaceIntSort(sort: Sort): Sort = sort match {
            case IntSort => newSort
            case x => x
        }

        // This is used to filter out terms that won't overflow (since we are currently casting them TO ints from an in bound constant)
        def withoutCastsToInt(terms: Seq[Term]): Seq[Term] = {
            terms.filter({
                case App(castToIntDefn.name, _) => false
                case _ => true
            })
        }

        // find function declarations that contain ints and therefore need to be changed
        val (intFunctions, otherFunctions) = problemState.theory.functionDeclarations.partition(decl => decl.argSorts.contains(IntSort) || decl.resultSort == IntSort)
        val oafIntFunctions = intFunctions.map({case FuncDecl(name, argSorts, resultSort) => {
            val newArgSorts = argSorts.map(replaceIntSort)
            val newResultSort = replaceIntSort(resultSort)
            FuncDecl(name, newArgSorts, newResultSort)
        }})

        /**
         *  Any arguments to a function that are OAF ints will need to be cast back to OAF ints
         * This function is designed to do that.
         * 
         * Returns a tuple. 
         * The first value is args all of the functions arguments properly wrapped in casts.
         * The second value is a sequence of (unwrapped) arguments that were changed, and thus need to be checked for overflows.
         */
        def castFunctionArgs(functionName: String, args: Seq[Term]): (Seq[Term], Seq[Term]) = {
            
            // find the declaration
            oafIntFunctions.find(_.name == functionName) match {
                case Some(decl) => {
                    // roll through the args, casting the OAF ints
                    var newArgs = scala.collection.mutable.Seq.from(args)
                    var currentIndex = decl.argSorts.indexOf(newSort)
                    // the terms which might overflow
                    var overflowableTerms:  Seq[Term] = Seq.empty
                    while (currentIndex != -1){
                        val termToCast = newArgs(currentIndex)
                        // the term when we cast it to the newSort 
                        val castTerm = castFromInt(termToCast)
                        newArgs.update(currentIndex, castTerm)
                        // add to overflowable terms only if we had to cast it 
                        castTerm match {
                            // We add before we cast because isInBounds takes an integer, not an OAF Int
                            case App(castFromIntDefn.name, _) => {overflowableTerms = overflowableTerms :+ termToCast}
                            case _ => {}
                        }
                        // find the next argument with an int (must be from a GREATER index)
                        currentIndex = decl.argSorts.indexOf(newSort, currentIndex+1)
                    }
                    (newArgs.toSeq, overflowableTerms)
                }
                // If we don't have a declaration, just apply without casting
                // TODO in the case of func
                case None => (args, Seq.empty)
            }
        }


        // We need to transform the definitions, but before we can do that, we cast them so we can use 
        var newConstDecls = problemState.theory.signature.constantDeclarations.map(_ match {
            case AnnotatedVar(variable, IntSort) => { 
                AnnotatedVar(variable, newSort)
            }
            case x => x
        })
        // TODO:
        /* We want definitions to still return/take in ints
         * BUT their internals can't quantify integers, etc.
         * So we must translate them, but not cast their args/output
         * We make the signature now, and do the replacement later, as transform must be defined.
         * 
         * Values in the definition might overflow and not reach a predicate.
         * Notably, the arguments of the function can cause this behavior.
         *      ex: f(x) := x + 1... f(a) = 5, we want to check if f(a) overflows, we can just use the f(a)
         *      f(x) := if x + 1 > 5 then x else x + 3 ... in this case does the if needs to be hoisted somehow?
         *          - We could conservatively say if the conditional is unknown then the next predicate 
         *              outside of the ITE should be unknown. It would be possible, though likely less efficient to do this raising
         * 
         */

        // Definitions will be removed and added later (we need to declare the data structures we will use here)
        val oldSig = problemState.theory.signature
        var newSignature = Signature(oldSig.sorts + newSort,
         otherFunctions ++ oafIntFunctions,
         oldSig.functionDefinitions + castToIntDefn + castFromIntDefn + isInBounds, // we need to translate the old sig later
         newConstDecls,
         oldSig.constantDefinitions, // We need to translate this later
         oldSig.enumConstants
        )
        
        // We will track replaced constants and definitions as well as their upInfo (any potential overflows inside)
        // Function Definitions can contain additional upInfo.
        // However, it is important to note their upInfo is in terms of the arguments, so we must substitute the appropriate values when using the function
        var changedConstDefnUps = scala.collection.mutable.Map.empty[String, UpInfo]
        var changedFuncDefnUps = scala.collection.mutable.Map.empty[String, UpInfo]



        def transform(term: Term, down: DownInfo = blankDown): (Term, UpInfo) = term match {
            case Exists(vars, body) => {
                // Change integers to oaf ints
                val (intVars, otherVars) = vars.partition(_.sort == IntSort)
                val newVars = intVars.map(iv => AnnotatedVar(iv.variable, newSort))
                // remove overwritten vars from those we will transform
                val overwrittenVars = otherVars.filter(ov => down.oafVars.contains(ov.variable))
                // remove quantified vars from raised checks
                val newDown = down
                    .withExtVars(newVars.map(_.variable))
                    .withoutVars(overwrittenVars.map(_.variable))
                    .withOtherVars(otherVars)

                val (newBody, upInfo) = transform(body, newDown)
                (Exists(newVars ++ otherVars, newBody), upInfo.excludingVars(newVars.map(_.variable)))
            }
            case Forall(vars, body) => {
                // Change integers to oaf ints
                val (intVars, otherVars) = vars.partition(_.sort == IntSort)
                val newVars = intVars.map(iv => AnnotatedVar(iv.variable, newSort))
                // remove overwritten vars from those we will transform
                val overwrittenVars = otherVars.filter(ov => down.oafVars.contains(ov.variable))
                // remove quantified vars from raised checks
                val newDown = down
                    .withoutVars(overwrittenVars.map(_.variable))
                    .withUnivVars(newVars.map(_.variable))
                    .withOtherVars(otherVars)

                val (newBody, upInfo) = transform(body, newDown)
                (Forall(newVars ++ otherVars, newBody), upInfo.excludingVars(newVars.map(_.variable)))
            }

            case Var(varName) => {
                val variable = Var(varName)
                if (down.oafVars.contains(variable)){
                    (castToInt(variable), blankUp)
                } else if (changedConstDefnUps.isDefinedAt(varName)){
                    // This is a constant definition with some upInfo, use that here
                    (variable, changedConstDefnUps(varName))
                } else {
                    (variable, blankUp)
                }
            }

            case App(functionName, arguments) => {
                // TODO change func defn Ups we need to substitute for the variables
                // we only translate like this for uninterpreted functions
                // As we generated a new sort, we only need to look at where that sort exists
                // We handled this earlier so we can ignore it here
                val (changedArgs, argUpInfos) = arguments.map(transform(_, down)).unzip
                val combinedArgsUp = combine(argUpInfos)
                // every arg we cast is a potential overflow
                val (castArgs, overflowTerms) = castFunctionArgs(functionName, changedArgs)
                // include the overflow terms in the upInfo
                var newUpInfo = combinedArgsUp.withOverflowableTerms(overflowTerms, down.universalVars, isInBounds.name)

                // Function Definitions can contain additional upInfo.
                // However, it is important to note their upInfo is in terms of the arguments, so we must substitute the appropriate values in
                val funcInfo = newSignature.queryFunction(functionName)
                funcInfo match {
                    case Some(Right(fdef)) => {
                        if (changedFuncDefnUps isDefinedAt functionName){
                            // Get the info that is rising from the changed definitions
                            val unsubstitutedUpInfo = changedFuncDefnUps(functionName)
                            // make the stubstitution
                            val varNames = fdef.argSortedVar.map(_.variable)
                            val substitutions: Map[Var, Term] = varNames.zip(castArgs).toMap
                            val substitutedDefinitionUpInfo = unsubstitutedUpInfo.substitute(substitutions, down.universalVars)

                            // change newUpInfo to include the values from the definition
                            newUpInfo = newUpInfo combine substitutedDefinitionUpInfo
                        }
                    }
                    case _ => {} // Otherwise do nothing
                }
                
                 
                // If the result sort is a boolean, this is a predicate and needs guards
                val resultSort = funcInfo match {
                    case None => Errors.Internal.preconditionFailed(f"signature does not contain function |${functionName}|")
                    case Some(Left(fdecl)) => fdecl.resultSort
                    case Some(Right(fdefn)) => fdefn.resultSort
                }
                val transformedApp = App(functionName, castArgs)
                if (resultSort == BoolSort){
                    val overflowProtectedApp = newUpInfo.overflowPredicate(transformedApp, down.polarity, isInBounds.name)
                    (overflowProtectedApp, newUpInfo)
                } else if (resultSort == newSort){
                    (castToInt(transformedApp), newUpInfo)
                }else {
                    (transformedApp, newUpInfo)
                }
            }

            // TODO does closure need to cast based on if the function has its types changed or not?
            case Closure(functionName, arg1, arg2, fixedArgs) => {
                val (transformedArgs, upInfos) = (Seq(arg1, arg2) ++ fixedArgs).map(transform(_, down)).unzip
                val upInfoFromBottom = combine(upInfos)
                val (castArgs, overflowTerms) = castFunctionArgs(functionName, transformedArgs)
                val newTerm = Closure(functionName, castArgs(0), castArgs(1), castArgs.slice(2, castArgs.length))
                val newUpInfo = upInfoFromBottom.withOverflowableTerms(overflowTerms, down.universalVars, isInBounds.name)
                (newTerm, newUpInfo)
            }

            case ReflexiveClosure(functionName, arg1, arg2, fixedArgs) => {
                val (transformedArgs, upInfos) = (Seq(arg1, arg2) ++ fixedArgs).map(transform(_, down)).unzip
                val upInfoFromBottom = combine(upInfos)
                val (castArgs, overflowTerms) = castFunctionArgs(functionName, transformedArgs)
                val newTerm = ReflexiveClosure(functionName, castArgs(0), castArgs(1), castArgs.slice(2, castArgs.length))
                val newUpInfo = upInfoFromBottom.withOverflowableTerms(overflowTerms, down.universalVars, isInBounds.name)
                (newTerm, newUpInfo)
            }

            case Eq(left, right) => {
                // Eq over booleans is essentially A & B | !A & !B,
                // In order to know the polarity we must split this up!
                // When it's not over booleans it's just a predicate
                val typecheckSig = newSignature
                    .withConstantDeclarations(down.existentialVars.toSeq.map(_ of newSort))
                    .withConstantDeclarations(down.universalVars.toSeq.map(_  of newSort))
                    .withConstantDeclarations(down.otherVars.map({case (v -> s ) => v of s})) // other vars 


                // We have to transform first
                val (transformedLeft, upLeft) = transform(left, down)

                var sort = transformedLeft.typeCheck(typecheckSig).sort
                if (sort == newSort) {
                    // If it hasn't been cast yet, it will be once we transform it
                    sort = IntSort
                }

                if (sort == IntSort){
                    // Transform the left and right
                    // val (transformedLeft, upLeft) = transform(left, down) // from above
                    val (transformedRight, upRight) = transform(right, down)

                    // We can ignore casting to int because we know it is in range
                    val overflowableTerms = Seq(transformedLeft, transformedRight).filter({
                        case App(castToIntDefn.name, _) => false 
                        case _ => true
                    })
                    
                    val upInfo = (upLeft combine upRight)
                        .withOverflowableTerms(overflowableTerms, down.universalVars, isInBounds.name)

                    val newEq = Eq(transformedLeft, transformedRight)
                    val guardedEq = upInfo.overflowPredicate(newEq, down.polarity, isInBounds.name)
                    (guardedEq, upInfo)
                } else if (sort == BoolSort) {
                    // A & B | !A & !B
                    //val (posLeft, upPosLeft) = transform(left, down) // from above
                    val (posLeft, upPosLeft) = (transformedLeft, upLeft) // from above
                    val (posRight, upPosRight) = transform(right, down)
                    val negatedDown = down.flipPolarity()
                    val (negLeft, upNegLeft) = transform(left, negatedDown)
                    val (negRight, upNegRight) = transform(right, negatedDown)

                    val upInfo = combine(Seq(upPosLeft, upPosRight, upNegLeft, upNegRight))
                    val unfoldedEq = Or(
                        And(posLeft, posRight),
                        And(negLeft, negRight)
                    )
                    (unfoldedEq, upInfo)
                } else {
                    // This is a predicate of other sorts, just flow up and guard (there could be int->A somewhere)
                    //val (transformedLeft, upLeft) = transform(left, down) // from above
                    val (transformedRight, upRight) = transform(right, down)

                    val newEq = Eq(transformedLeft, transformedRight)
                    val upInfo = (upLeft combine upRight)
                    val guardedEq = upInfo.overflowPredicate(newEq, down.polarity, isInBounds.name)

                    (guardedEq, upInfo)
                }
            }            
            
            case Not(body) => {
                val (transfomedBody, up) = transform(body, down.flipPolarity)
                (Not(transfomedBody), up)
            }
            case AndList(arguments) => {
                val (transformedArgs, upInfos) = arguments.map(transform(_, down)).unzip
                (AndList(transformedArgs), combine(upInfos))
            }
            case OrList(arguments) => {
                val (transformedArgs, upInfos) = arguments.map(transform(_, down)).unzip
                (OrList(transformedArgs), combine(upInfos))
            }


            case IfThenElse(condition, ifTrue, ifFalse) => {
                val (transformedCondition, upCondition) = transform(condition, down)
                val (transformedIfTrue, upTrue) = transform(ifTrue, down)
                val (transformedIfFalse, upFalse) = transform(ifFalse, down)

                // up Does not overflow when all of its overflows are false
                // Or.smart will default to false if no values included
                val upDoesNotOverflow = Not(Or.smart(upCondition.univQuantChecks.toSeq ++ upCondition.extQuantChecks.toSeq))
                // branches only cause an overflow if we actually use the value there
                val overflowUniv = AndList(upDoesNotOverflow, 
                    IfThenElse(transformedCondition, Or.smart(upTrue.univQuantChecks.toSeq), Or.smart(upFalse.univQuantChecks.toSeq))
                    )
                val overflowExt = AndList(upDoesNotOverflow, 
                    IfThenElse(transformedCondition, Or.smart(upTrue.extQuantChecks.toSeq), Or.smart(upFalse.extQuantChecks.toSeq))
                    )
                // We only use the condensed overflows
                val newUp = UpInfo(upCondition.extQuantChecks + overflowExt, upCondition.univQuantChecks + overflowUniv)
                val transformedITE = IfThenElse(transformedCondition, transformedIfTrue, transformedIfFalse)

                // predicate needs to be wrapped with the conditional's ability to overflow (the branches should already be handled)
                val resultSort = ifTrue.typeCheck(down.typeCheckSig(newSignature, newSort)).sort
                if (resultSort == BoolSort){
                    val guardedITE = newUp.overflowPredicate(transformedITE, down.polarity, isInBounds.name)
                    (guardedITE, newUp)
                } else {
                    (transformedITE, newUp)
                }
                
            }
            case BuiltinApp(function, arguments) => {
                val isIntPredicate = function.resultSortFromArgSorts(Seq(IntSort, IntSort)) match {
                    case Some(BoolSort) => true
                    case _ => false
                }
                val (transformedArgs, upInfos) = arguments.map(transform(_, down)).unzip
                val newBuiltinApp = BuiltinApp(function, transformedArgs)
                var upInfo = combine(upInfos)
                if (isIntPredicate){
                    // Add overflow checks
                    val overflowableArgs = withoutCastsToInt(transformedArgs)
                    upInfo = upInfo.withOverflowableTerms(overflowableArgs, down.universalVars, isInBounds.name)
                    val guardedBuiltinApp = upInfo.overflowPredicate(newBuiltinApp, down.polarity, isInBounds.name)
                    (guardedBuiltinApp, upInfo)
                } else {
                    // just pass through
                    (newBuiltinApp, upInfo)
                }
                
            }
            case Distinct(arguments) => {
                val (transformedArgs, upInfos) = arguments.map(transform(_, down)).unzip
                (Distinct(transformedArgs), combine(upInfos)) // todo check overflow?
            }
            case Implication(left, right) => {
                // A => B == !A || B so left has flipped polarity
                val (transformedLeft, upLeft) = transform(left, down.flipPolarity)
                val (transformedRight, upRight) = transform(right, down)
                (Implication(transformedLeft, transformedRight), upLeft combine upRight)
            }
            case Iff(left, right) => {
                // Eq over booleans is essentially A & B | !A & !B
                // We have to do this because the polarity goes both ways here
                // We can't default A to be true or false if we don't know what B is
                val (posLeft, upLeft) = transform(left, down)
                val (posRight, upRight) = transform(right, down)
                val (negLeft, upNegLeft) = transform(left, down.flipPolarity)
                val (negRight, upNegRight) = transform(right, down.flipPolarity)

                val newUp = upLeft.combine(Seq(upNegLeft, upRight, upNegRight))
                val newTerm = Or(And(posLeft, posRight), And(negLeft, negRight))
                (newTerm, newUp)
            }
            
            case IntegerLiteral(value) => (IntegerLiteral(value), blankUp)
            case DomainElement(index, sort) => (DomainElement(index, sort), blankUp)
            case BitVectorLiteral(value, bitwidth) => (BitVectorLiteral(value, bitwidth), blankUp)
            case EnumValue(name) => (EnumValue(name), blankUp)
            case Top => (Top, blankUp)
            case Bottom => (Bottom, blankUp)
        }
        

        // Integer constants are existentially quantified
        val intConstants: Set[Var] = newSignature.constantDeclarations.filter(_.sort == newSort).map(_.variable)
        val startingDown = DownInfo(intConstants, Set.empty, true, Map.empty)
        
        // The upInfo from definitions is used in the normal transformations, so we need to change them first

        for (defn <- oldSig.definitionsInDependencyOrder()){
            defn match {
                case Left(cDef) => {
                    newSignature = newSignature.withoutConstantDefinition(cDef)
                    val (newBody, upInfo) = transform(cDef.body, startingDown)
                    changedConstDefnUps.addOne(cDef.name -> upInfo)
                    newSignature = newSignature.withConstantDefinition(cDef.copy(body=newBody))
                }
                case Right(fDef) => {
                    newSignature = newSignature.withoutFunctionDefinition(fDef)
                    
                    // Our downinfo must contain the information for the arguments for typechecking
                    val down = startingDown withOtherVars fDef.argSortedVar
                    
                    val (newBody, upInfo) = transform(fDef.body, down)
                    changedFuncDefnUps.addOne(fDef.name -> upInfo)
                    newSignature = newSignature.withFunctionDefinition(fDef.copy(body = newBody))
                }
            }
        }
        /*
        // now we change newSignature's definitions
        for(cDef <- oldSig.constantDefinitions){
            newSignature = newSignature.withoutConstantDefinition(cDef)
            val (newBody, upInfo) = transform(cDef.body, startingDown)
            newSignature = newSignature.withConstantDefinition(cDef.copy(body = newBody))
        }

        for(fDef <- oldSig.functionDefinitions){
            val name = fDef.name
            if (name == castToIntDefn.name || name == castFromIntDefn.name || name == isInBounds.name){
                // Do nothing
            } else {
                newSignature = newSignature.withoutFunctionDefinition(fDef)

                // Our downinfo must contain the information for the arguments for typechecking
                val down = startingDown withOtherVars fDef.argSortedVar

                val (newBody, upInfo) = transform(fDef.body, down)
                newSignature = newSignature.withFunctionDefinition(fDef.copy(body = newBody))
            } 
        }

        */

        
        // transform the axioms
        val (newAxioms, upInfos) = problemState.theory.axioms.map(transform(_, startingDown)).unzip
        
        // This is specifically not transformed
        //val constantsAreDistinct = Distinct(intToConstants.values.toSeq)
        //val allNewAxioms = newAxioms + constantsAreDistinct
        val allNewAxioms = newAxioms

        // We unapply by converting calculated values back to integers
        val constantsToIntLits: Map[Value, Value] = constantsToInts.mapValues(IntegerLiteral(_)).toMap
        def unapplyInterp(interp: Interpretation): Interpretation = {
            val substitute = new ValuedSortSubstitution(Map(newSort -> IntSort), constantsToIntLits)
            interp.applySortSubstitution(substitute)
        }

        // could this be done with domain elements? Yes. Should it... probably? TODO
        val newTheory = Theory(newSignature, allNewAxioms)
        problemState.withScopes(newScopes).withTheory(newTheory)
            .withUnapplyInterp(unapplyInterp)
    }

    // Info passed down through transform
    // These are oaf vars which must be cast now
    case class DownInfo(existentialVars: Set[Var], universalVars: Set[Var], polarity: Boolean, otherVars: Map[Var, Sort]){
        // oafVars are variables that are being cast to oaf vars
        def withExtVar(v: Var): DownInfo = {
            DownInfo(existentialVars + v, universalVars, polarity, otherVars)
        }
        def withExtVars(vs: Seq[Var]): DownInfo = {
            DownInfo(existentialVars union vs.toSet, universalVars, polarity, otherVars)
        }
        def withUnivVar(v: Var): DownInfo = {
            DownInfo(existentialVars, universalVars + v, polarity, otherVars)
        }
        def withUnivVars(vs: Seq[Var]): DownInfo = {
            DownInfo(existentialVars, universalVars union vs.toSet, polarity, otherVars)
        }
        def withoutVar(v: Var): DownInfo = {
            DownInfo(existentialVars - v, universalVars - v, polarity, otherVars)
        }
        def withoutVars(vs: Seq[Var]): DownInfo = {
            DownInfo(existentialVars diff vs.toSet, universalVars diff vs.toSet, polarity, otherVars)
        }

        def withOtherVars(aVars: Seq[AnnotatedVar]): DownInfo = {
            DownInfo(existentialVars, universalVars, polarity, otherVars ++ (aVars.map(av => av.variable -> av.sort)))
        }
        // Both existential and universal Vars
        val oafVars: Set[Var] = {
            existentialVars union universalVars
        }
        def flipPolarity(): DownInfo = DownInfo(existentialVars, universalVars, !polarity, otherVars)

        def typeCheckSig(currentSignature: Signature, newSort: Sort): Signature = currentSignature
            .withConstantDeclarations(existentialVars.toSeq.map(_ of newSort))
            .withConstantDeclarations(universalVars.toSeq.map(_  of newSort))
            .withConstantDeclarations(otherVars.map({case (v -> s ) => v of s}))
    }
    val blankDown = DownInfo(Set.empty, Set.empty, true, Map.empty)
    // Info passed back up through transform
    case class UpInfo(extQuantChecks: Set[Term], univQuantChecks: Set[Term]){
        //These checks are BoolSort and should evaluate to true if an overflow occurs 

        def combine(other: UpInfo): UpInfo = {
            UpInfo(extQuantChecks union other.extQuantChecks, univQuantChecks union other.univQuantChecks)
        }
        def combine(others:Seq[UpInfo]): UpInfo = {
            others.foldLeft(this)(_.combine(_))
        }
        // Add the terms into the correct set (ext or univ)
        // The overflowTerms should NOT be wrapped
        /**
          * Separates terms which could overflow into existential and univ, then wraps them in !isInBounds(...)
          * This makes them checks
          *
          * @param overflowTerms Terms that can overflow (these should be IntSort, not BoolSort)
          * @param universalVars The set of universally quantified NewSort values 
          * @return
          */
        def withOverflowableTerms(overflowTerms: Seq[Term], universalVars: Set[Var], isInBoundsName: String): UpInfo = {
            val (extTerms, univTerms) = overflowTerms.partition( term => {
                val varsin = RecursiveAccumulator.freeVariablesIn(term)
                (varsin intersect universalVars).isEmpty
            })
            // wrap the checks
            val extChecks = extTerms.map(term => Not(App(isInBoundsName, Seq(term))))
            val univChecks = univTerms.map(term => Not(App(isInBoundsName, Seq(term))))
            UpInfo(extQuantChecks union extChecks.toSet, univQuantChecks union univChecks.toSet)
        }

        def withUnivChecks(univChecks: Set[Term]): UpInfo = {
            copy(univQuantChecks = univQuantChecks union univChecks)
        }
        def withExtChecks(extChecks: Set[Term]): UpInfo = {
            copy(extQuantChecks = extQuantChecks union extChecks)
        }

        /**
         * Removes overflows checks that contain any of the variables provided.
         * This is useful for quantifiers, that do not want to raise overflow checks for variables they quantified.
         */
        def excludingVars(vars: Seq[Var]): UpInfo = {
            val setVars = vars.toSet
            val overflowContainsVars: Function[Term, Boolean] = overflow =>{
                val variables = RecursiveAccumulator.freeVariablesIn(overflow)
                // check if anty overlap occurs
                !(setVars & variables).isEmpty
            }
            // remove 
            UpInfo(extQuantChecks.filterNot(overflowContainsVars),
            univQuantChecks.filterNot(overflowContainsVars))
        }

        /**
          * Applies no overflow semantics wrapper to a term
          * @param term the predicate term that may contain an overflow value
          */
        def overflowPredicateOld(term: Term, polarity: Boolean, isInBoundsName: String): Term = {
            // Note we check is in bounds, while ensureDfn uses == unknown, so our negations are backwards 
            val bDef = if (extQuantChecks.isEmpty) {Top} else {
                val negatedChecks = extQuantChecks.toSeq // .map( term => App(isInBoundsName, term)) // Removed as we now check at input
                // And/Or list must have more than 1 argument, so if only one just give back the original value
                if (negatedChecks.length == 1) {
                    negatedChecks(0)
                } else {
                    AndList(negatedChecks)
                }
            }
            val bUndef = if (univQuantChecks.isEmpty) {Bottom} else {
                val checks = extQuantChecks.toSeq// .map(term => Not(App(isInBoundsName, term))) // Removed as we now check at input
                // And/Or list must have more than 1 argument, so if only one just give back the original value
                if (checks.length == 1) {
                    checks(0)
                } else {
                    OrList(checks)
                }
            }
            // different value based on polarity. cases used to simplify quickly
            if (polarity) {
                // And(Or(term, bUndef), bDef)
                (bUndef, bDef) match {
                    case (Bottom, Top) => term
                    case (Bottom, _) => And(term, bDef)
                    case (_, Top) => Or(term, bUndef)
                    case _ => And(Or(term, bUndef), bDef)
                }
            } else {
                // And(Or(term, Not(bDef)), Not(bUndef))
                (bDef, bUndef) match {
                    case (Top, Bottom) => term
                    case (Top, _) => And(term, Not(bUndef))
                    case (_, Bottom) => Or(term, Not(bDef))
                    case _ => And(Or(term, Not(bDef)), Not(bUndef))
                }
            }
        }

        def overflowPredicate(term: Term, polarity: Boolean, isInBoundsName: String): Term = {
            // Disjunction of all possible overflows as we just want to know if any possible way it overflows
            val univOverflows = univQuantChecks.size match {
                case 0 => Bottom
                case 1 => univQuantChecks.head // gets the singleton from the set
                case _ => OrList(univQuantChecks.toSeq)
            }
            val extOverflows = extQuantChecks.size match {
                case 0 => Bottom
                case 1 => extQuantChecks.head // gets the singleton from the set
                case _ => OrList(extQuantChecks.toSeq)
            }

            // Automatically simplify out when a set is already Bottom
            if (polarity) {
                (univOverflows, extOverflows) match {
                    case (Bottom, Bottom) => term
                    case (Bottom, _) => And(term, Not(extOverflows))
                    case (_, Bottom) => Or(term, univOverflows)
                    case _ => And(Or(term, univOverflows), Not(extOverflows))
                }
            } else {
                (univOverflows, extOverflows) match {
                    case (Bottom, Bottom) => term
                    case (Bottom, _) => Or(term, extOverflows)
                    case (_, Bottom) => And(term, Not(univOverflows))
                    case _ => And(Or(term, extOverflows), Not(univOverflows))
                }
            }
        }

        /**
          * Make the given substitutions in each check. Useful for function definitions' upinfo.
          * Substitutions can change if something is univ or ext, so we need to repartition them
          * @param substitutions
          * @return
          */
        def substitute(substitutions: Map[Var, Term], univVars: Set[Var]): UpInfo = {
            val allChecks = extQuantChecks.map(_.fastSubstitute(substitutions)) union univQuantChecks.map(_.fastSubstitute(substitutions))
            val (newExtChecks, newUnivChecks) = allChecks.partition(RecursiveAccumulator.freeVariablesIn(_).intersect(univVars).isEmpty)
            UpInfo(newExtChecks, newUnivChecks)
        }
    }
    
    def combine(upInfos: Seq[UpInfo]): UpInfo = {
        upInfos(0).combine(upInfos.slice(1, upInfos.size))
    }
    val blankUp = UpInfo(Set.empty, Set.empty)
}