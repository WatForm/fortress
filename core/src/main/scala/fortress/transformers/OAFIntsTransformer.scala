package fortress.transformers

import fortress.problemstate.ProblemState
import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.TermOps._
import fortress.operations.RecursiveAccumulator
import fortress.problemstate.ExactScope
import fortress.util.Errors

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

        val isInBounds: FunctionDefinition = FunctionDefinition(varNameGenerator.freshName(f"isInBoundsOAF"), Seq(x.of(IntSort)), BoolSort,
            AndList(
                Term.mkGE(IntegerLiteral(min), x),
                Term.mkLE(IntegerLiteral(max), x)
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
                case None => (args, Seq.empty)
            }
        }

        var changedConstants: Seq[Var] = Seq.empty
        var newConstants = problemState.theory.signature.constantDeclarations.map(_ match {
            case AnnotatedVar(variable, IntSort) => {
                changedConstants = changedConstants :+ variable   
                AnnotatedVar(variable, newSort)
            }
            case x => x
        })

        val oldSig = problemState.theory.signature
        val newSignature = Signature(oldSig.sorts + newSort,
         otherFunctions ++ oafIntFunctions,
         oldSig.functionDefinitions + castToIntDefn + castFromIntDefn + isInBounds,
         newConstants,
         oldSig.constantDefinitions, // TODO absolutely wrong
         oldSig.enumConstants
        )



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
                    .withExtVars(newVars.map(_.variable))
                    .withoutVars(overwrittenVars.map(_.variable))
                    .withOtherVars(otherVars)

                val (newBody, upInfo) = transform(body, newDown)
                (Forall(newVars ++ otherVars, newBody), upInfo.excludingVars(newVars.map(_.variable)))
            }

            case Var(varName) => {
                val variable = Var(varName)
                if (down.oafVars.contains(variable)){
                    (castToInt(variable), blankUp)
                } else {
                    (variable, blankUp)
                }
            }

            case App(functionName, arguments) => {
                // we only translate like this for uninterpreted functions
                // As we generated a new sort, we only need to look at where that sort exists
                // We handled this earlier so we can ignore it here
                // TODO overflow checks if predicate
                val (changedArgs, upInfos) = arguments.map(transform(_, down)).unzip
                val upInfoFromBottom = combine(upInfos)
                // every arg we cast is a potential overflow
                val (castArgs, overflowTerms) = castFunctionArgs(functionName, changedArgs)
                // include the overflow terms in the upInfo
                val newUpInfo = upInfoFromBottom.withOverflows(overflowTerms, down.universalVars)
                
                val resultSort = newSignature.queryFunction(functionName) match {
                    case None => Errors.Internal.preconditionFailed(f"signature does not contain function |${functionName}|")
                    case Some(Left(fdecl)) => fdecl.resultSort
                    case Some(Right(fdefn)) => fdefn.resultSort
                }
                val castApp = App(functionName, castArgs)
                if (resultSort == BoolSort){
                    val overflowProtectedApp = newUpInfo.overflowPredicate(castApp, down.polarity, isInBounds.name)
                    (overflowProtectedApp, newUpInfo)
                } else {
                    (castApp, newUpInfo)
                }
            }


            case Closure(functionName, arg1, arg2, fixedArgs) => {
                val (transformedArgs, upInfos) = (Seq(arg1, arg2) ++ fixedArgs).map(transform(_, down)).unzip
                val upInfoFromBottom = combine(upInfos)
                val (castArgs, overflowTerms) = castFunctionArgs(functionName, transformedArgs)
                val newTerm = Closure(functionName, castArgs(0), castArgs(1), castArgs.slice(2, castArgs.length))
                val newUpInfo = upInfoFromBottom.withOverflows(overflowTerms, down.universalVars)
                (newTerm, newUpInfo)
            }

            case ReflexiveClosure(functionName, arg1, arg2, fixedArgs) => {
                val (transformedArgs, upInfos) = (Seq(arg1, arg2) ++ fixedArgs).map(transform(_, down)).unzip
                val upInfoFromBottom = combine(upInfos)
                val (castArgs, overflowTerms) = castFunctionArgs(functionName, transformedArgs)
                val newTerm = ReflexiveClosure(functionName, castArgs(0), castArgs(1), castArgs.slice(2, castArgs.length))
                val newUpInfo = upInfoFromBottom.withOverflows(overflowTerms, down.universalVars)
                (newTerm, newUpInfo)
            }

            case Eq(left, right) => {
                val (transformedLeft, upLeft) = transform(left, down)
                val (transformedRight, upRight) = transform(right, down)
                // We need to know the type here because ints need to be overflow checked
                // TODO quantified variables are in here. Probably works to just say with constants, but then we need to take more info down with us
                //    ... specifically the sorts of every variable
                val typecheckSig = newSignature
                    .withConstantDeclarations(down.existentialVars.toSeq.map(_ of newSort))
                    .withConstantDeclarations(down.universalVars.toSeq.map(_  of newSort))
                    .withConstantDeclarations(down.otherVars.map({case (v -> s ) => v of s})) // other vars 

                val sort = transformedLeft.typeCheck(typecheckSig).sort
                var upInfo = (upLeft combine upRight)

                // if it is an int, we must check for overflows
                val newEq = Eq(transformedLeft, transformedRight)
                if (sort == IntSort){
                    // Add the overflow checks to the upInfo
                    // They should be before the guards are added, but we don't add guards for EQ
                    // We don't need to add anything casting ToInts
                    val overflowableTerms = Seq(transformedLeft, transformedRight).filter({
                        case App(castToIntDefn.name, _) => false 
                        case _ => true
                    })
                    upInfo = upInfo.withOverflows(overflowableTerms, down.universalVars)
                    // apply overflow checks
                    val guardedEq = upInfo.overflowPredicate(newEq, down.polarity, isInBounds.name)
                    (guardedEq, upInfo) 
                } else {
                    (newEq, upInfo)
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
            // NOTE does ITE need to be broken up with a new value to hold it's result?
            // Specifically if there is an overflow in the condition how does this work out?
            case IfThenElse(condition, ifTrue, ifFalse) => {
                val (transformedCondition, upCondition) = transform(condition, down)
                val (transformedIfTrue, upTrue) = transform(ifTrue, down)
                val (transformedIfFalse, upFalse) = transform(ifFalse, down)
                val newUp = upCondition combine upTrue combine upFalse
                (IfThenElse(transformedCondition, transformedIfTrue, transformedIfFalse), newUp)
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
                    upInfo = upInfo.withOverflows(overflowableArgs, down.universalVars)
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
                val (transformedLeft, upLeft) = transform(left, down)
                val (transformedRight, upRight) = transform(right, down)
                (Iff(transformedLeft, transformedRight), upLeft combine upRight) // should be bools only, can this have int args?
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
        // transform the axioms
        val (newAxioms, upInfos) = problemState.theory.axioms.map(transform(_, startingDown)).unzip
        // This is specifically not transformed
        //val constantsAreDistinct = Distinct(intToConstants.values.toSeq)
        //val allNewAxioms = newAxioms + constantsAreDistinct
        val allNewAxioms = newAxioms
        // could this be done with domain elements? Yes. Should it... probably? TODO
        val newTheory = Theory(newSignature, allNewAxioms)
        problemState.withScopes(newScopes).withTheory(newTheory)
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
    }
    val blankDown = DownInfo(Set.empty, Set.empty, true, Map.empty)
    // Info passed back up through transform
    case class UpInfo(extQuantOverflows: Set[Term], univQuantOverflows: Set[Term]){
        def combine(other: UpInfo): UpInfo = {
            UpInfo(extQuantOverflows union other.extQuantOverflows, univQuantOverflows union other.univQuantOverflows)
        }
        def combine(others:Seq[UpInfo]): UpInfo = {
            others.foldLeft(this)(_.combine(_))
        }
        // Add the terms into the correct set (ext or univ)
        // The overflowTerms should NOT be wrapped
        def withOverflows(overflowTerms: Seq[Term], universalVars: Set[Var]): UpInfo = {
            val (extTerms, univTerms) = overflowTerms.partition( term => {
                (RecursiveAccumulator.freeVariablesIn(term) & universalVars).isEmpty
            })
            UpInfo(extQuantOverflows union extTerms.toSet, univQuantOverflows union univTerms.toSet)
        }

        /**
         * Removes overflows that contain any of the variables provided.
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
            UpInfo(extQuantOverflows.filterNot(overflowContainsVars),
            univQuantOverflows.filterNot(overflowContainsVars))
        }

        /**
          * Applies no overflow semantics wrapper to a term
          * @param term the predicate term that may contain an overflow value
          */
        def overflowPredicate(term: Term, polarity: Boolean, isInBoundsName: String): Term = {
            // Note we check is in bounds, while ensureDfn uses == unknown, so our negations are backwards 
            val bDef = if (extQuantOverflows.isEmpty) {Top} else {
                val negatedChecks = extQuantOverflows.toSeq.map( term => App(isInBoundsName, term))
                // And/Or list must have more than 1 argument, so if only one just give back the original value
                if (negatedChecks.length == 1) {
                    negatedChecks(0)
                } else {
                    AndList(negatedChecks)
                }
            }
            val bUndef = if (univQuantOverflows.isEmpty) {Bottom} else {
                val checks = extQuantOverflows.toSeq.map(term => Not(App(isInBoundsName, term)))
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
    }
    def combine(upInfos: Seq[UpInfo]): UpInfo = {
        upInfos(0).combine(upInfos.slice(1, upInfos.size))
    }
    val blankUp = UpInfo(Set.empty, Set.empty)
}