package fortress.transformers

import fortress.problemstate.ProblemState
import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.operations.TermOps._
import fortress.operations.RecursiveAccumulator
import fortress.problemstate.ExactScope

object OAFIntsTransformer extends ProblemStateTransformer {
    val name: String = "OAFIntsTransformer"

    // Generate mapping using min, max inclusive
    def generateConstantMapping(min: Int, max: Int, varNameGenerator: NameGenerator): Map[Int, Var] = {
        Range(min, max+1).map(intValue => intValue -> Var(varNameGenerator.freshName(f"OAF${intValue}"))).toMap
    }

    def apply(problemState: ProblemState): ProblemState = {
        // We don't want to replicate existing functions or variables or constants
        val forbiddenNames: Set[String] = (
            problemState.theory.constants.map(_.name) union problemState.theory.functionDeclarations.map(_.name) union
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

        val newScopes = problemState.scopes + (newSort -> ExactScope(max - min, true))

        val intToConstants: Map[Int, Var] = generateConstantMapping(min, max, varNameGenerator)
        val constantsToInts: Map[Var, Int] = intToConstants.map({ case (ival, varVal) => varVal -> ival})
        // generate interpreted functions to do casting
        val castToIntDefn: FunctionDefinition = FunctionDefinition(varNameGenerator.freshName(f"cast${newSort.name}ToInt"), Seq(ax), IntSort,
            // Generate the body by folding to make If(x == v1) then {1} else {If (x == v2) then {2} else {...  else {<any dummy value>}}}
            constantsToInts.foldLeft(IntegerLiteral(min): Term)({case (prev, (constValue, intValue)) => IfThenElse(Eq(x, constValue), IntegerLiteral(intValue), prev)})
        )
        val castFromIntDefn: FunctionDefinition = FunctionDefinition(varNameGenerator.freshName(f"castIntTo${newSort.name}"), Seq(ax), newSort,
            intToConstants.foldLeft(intToConstants(min): Term)({ case (prev, (intValue, constValue)) => IfThenElse(Eq(x, IntegerLiteral(intValue)), constValue, prev)})
        )

        val isInBounds: FunctionDefinition = FunctionDefinition(varNameGenerator.freshName(f"isInBounds${newSort.name}"), Seq(ax), BoolSort,
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

        // find function declarations that contain ints and therefore need to be changed
        val (intFunctions, otherFunctions) = problemState.theory.functionDeclarations.partition(decl => decl.argSorts.contains(newSort) || decl.resultSort == newSort)
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
                    var castTerms: Seq[Term] = Seq.empty
                    while (currentIndex != -1){
                        castTerms = castTerms :+ newArgs(currentIndex)
                        newArgs.update(currentIndex, castFromInt(newArgs(currentIndex)))
                        
                        currentIndex = decl.argSorts.indexOf(newSort, currentIndex)
                    }
                    (newArgs.toSeq, castTerms)
                }
                // If we don't have a declaration, just apply without casting
                case None => (args, Seq.empty)
            }
        }

        var changedConstants: Seq[Var] = Seq.empty
        var newConstants = problemState.theory.signature.constants.map(_ match {
            case AnnotatedVar(variable, IntSort) => {
                changedConstants = changedConstants :+ variable   
                AnnotatedVar(variable, newSort)
            }
            case x => x
        })

        val oldSig = problemState.theory.signature
        val newSignature = Signature(oldSig.sorts + newSort,
         otherFunctions ++ oafIntFunctions,
         oldSig.functionDefinitions + castToIntDefn + castFromIntDefn,
         newConstants,
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
                val newDown = down.withExtVars(newVars.map(_.variable)).withoutVars(overwrittenVars.map(_.variable))

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
                val newDown = down.withExtVars(newVars.map(_.variable)).withoutVars(overwrittenVars.map(_.variable))

                val (newBody, upInfo) = transform(body, newDown)
                (Forall(newVars ++ otherVars, newBody), upInfo.excludingVars(newVars.map(_.variable)))
            }

            case variable: Var => {
                if (down.oafVars.contains(variable)){
                    (castToInt(variable), blankUp)
                } else {
                    (variable, blankUp)
                }
            }

            case App(functionName, arguments) => {
                // TODO overflow checks if predicate
                val (changedArgs, upInfos) = arguments.map(transform(_, down)).unzip
                val upInfoFromBottom = combine(upInfos)
                // every arg we cast is a potential overflow
                val (castArgs, overflowTerms) = castFunctionArgs(functionName, changedArgs)

                val newUpInfo = upInfoFromBottom.withOverflows(overflowTerms, down.universalVars)
                (App(functionName, castArgs), newUpInfo)
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
                // We need to know the type here
                val sort = left.typeCheck(newSignature).sort
                val (transformedLeft, upLeft) = transform(left, down)
                val (transformedRight, upRight) = transform(right, down)
                var upInfo = (upLeft combine upRight)
                // if it is an int, we must check for overflows
                if (sort == newSort){
                    // Add the overflow checks to the upInfo
                    // They should be before the guards are added, but we don't add guards for EQ
                    upInfo = upInfo.withOverflows(Seq(transformedLeft, transformedRight), down.universalVars)
                    // TODO overflow checks
                    val newEq = Eq(transformedLeft, transformedRight)
                    val guardedEq = upInfo.overflowPredicate(newEq, down.polarity, isInBounds.name)
                    (newEq, upInfo)
                }
                (Eq(transformedLeft, transformedRight), upInfo)
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
                    upInfo = upInfo.withOverflows(arguments, down.universalVars)
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
        
        val (newAxioms, upInfos) = problemState.theory.axioms.map(transform(_)).unzip
        val newTheory = Theory(newSignature, newAxioms)
        problemState.withScopes(newScopes).withTheory(newTheory)
    }

    // Info passed down through transform
    // These are oaf vars which must be cast now
    case class DownInfo(existentialVars: Set[Var], universalVars: Set[Var], polarity: Boolean){
        // oafVars are variables that are being cast to oaf vars
        def withExtVar(v: Var): DownInfo = {
            DownInfo(existentialVars + v, universalVars, polarity)
        }
        def withExtVars(vs: Seq[Var]): DownInfo = {
            DownInfo(existentialVars union vs.toSet, universalVars, polarity)
        }
        def withUnivVar(v: Var): DownInfo = {
            DownInfo(existentialVars, universalVars + v, polarity)
        }
        def withUnivVars(vs: Seq[Var]): DownInfo = {
            DownInfo(existentialVars, universalVars union vs.toSet, polarity)
        }
        def withoutVar(v: Var): DownInfo = {
            DownInfo(existentialVars - v, universalVars - v, polarity)
        }
        def withoutVars(vs: Seq[Var]): DownInfo = {
            DownInfo(existentialVars diff vs.toSet, universalVars diff vs.toSet, polarity)
        }
        // Both existential and universal Vars
        val oafVars: Set[Var] = {
            existentialVars union universalVars
        }
        val flipPolarity: DownInfo = DownInfo(existentialVars, universalVars, !polarity)
    }
    val blankDown = DownInfo(Set.empty, Set.empty, true)
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
            val bDef = if (extQuantOverflows.isEmpty) {Top} else {
                AndList(extQuantOverflows.toSeq.map( term => Not(App(isInBoundsName, term))))
            }
            val bUndef = if (univQuantOverflows.isEmpty) {Bottom} else {
                OrList(extQuantOverflows.toSeq.map(App(isInBoundsName, _)))
            }
            if (polarity) {
                And(Or(term, bUndef), bDef)
            } else {
                And(Or(term, Not(bDef), Not(bUndef)))
            }
        }
    }
    def combine(upInfos: Seq[UpInfo]): UpInfo = {
        upInfos(0).combine(upInfos.slice(1, upInfos.size))
    }
    val blankUp = UpInfo(Set.empty, Set.empty)
}