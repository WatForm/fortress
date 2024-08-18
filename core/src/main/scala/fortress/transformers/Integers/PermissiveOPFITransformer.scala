package fortress.transformers.Integers

import fortress.transformers.ProblemStateTransformer
import fortress.problemstate.ProblemState
import fortress.msfol._
import fortress.data.NameGenerator
import fortress.data.IntSuffixNameGenerator
import fortress.problemstate.ExactScope

object Polarity extends Enumeration {
    type Polarity = Value
    val Positive, Negative, Indeterminate = Value

    def flip(p: Polarity) = p match {
        case Positive => Negative
        case Negative => Positive
        case Indeterminate => Indeterminate
    }
}
import Polarity._

object PermissiveOPFITransformer extends ProblemStateTransformer {
    // Generate mapping using min, max inclusive
    def generateConstantMapping(min: Int, max: Int, sort: Sort): Map[Int, DomainElement] = {
        Range(min, max+1).map(intValue => intValue -> DomainElement(intValue - min + 1, sort)).toMap
    }

    def unionAll[A](sets: Seq[Set[A]]): Set[A] = {
        sets reduce (_ union _)
    }

    def unknown(checks: Set[Term]): Term = OrList(checks.toSeq)

    // If a value would overflow, set it to false
    def knownOrFalse(term: Term, checks: Set[Term]): Term = {
        if (checks.isEmpty){
            term
        } else {
            // term & !(check0 | check1 | ...)
            And(term, Not(unknown(checks)))
        }
    }

    // If a value would overflow, set it to true
    def knownOrTrue(term: Term, checks: Set[Term]): Term = {
        if (checks.isEmpty){
            term
        } else {
            // term & !(check0 | check1 | ...)
            And(term, unknown(checks))
        }
    }

    // If a value is known and true
    def knownAndTrue(term: Term, checks: Set[Term]): Term = {
        if (checks.isEmpty){
            term
        } else {
            And(term, Not(unknown(checks)))
        }
    }

    // If a value is known and false
    def knownAndFalse(term: Term, checks: Set[Term]): Term = {
        if (checks.isEmpty){
            Not(term)
        } else {
            And(Not(term), Not(unknown(checks)))
        }
    }

    def apply(problemState: ProblemState): ProblemState = {
        // early leave if we don't have a scope for the intsort
        if (!problemState.scopes.isDefinedAt(IntSort)){
            return problemState
        }

        // We don't want to replicate existing functions or variables or constants
        val forbiddenNames: Set[String] = (
            problemState.theory.constantDeclarations.map(_.name) union problemState.theory.functionDeclarations.map(_.name) union
            problemState.theory.functionDefinitions.map(_.name) union
            problemState.theory.constantDefinitions.map(_.name)
        ).toSet
        val varNameGenerator: NameGenerator = new IntSuffixNameGenerator(forbiddenNames, 0)

        // sorts have their own exclusive names
        val sortNames = problemState.theory.signature.sorts.map(_.name)
        val sortNameGenertor = new IntSuffixNameGenerator(sortNames, 0)

        val opfiSort = SortConst(sortNameGenertor.freshName("OPFInt"))

        // vars to write more efficiently
        val x = Var("x")
        val z = Var("z")
        val y = Var("y")
        val ax = x.of(opfiSort)
        val ay = y.of(opfiSort)
        val az = z.of(opfiSort)
        val axy = Seq(ax, ay)
        val axyz = Seq(ax, ay, az)

        // Calculate the range
        val numValues = problemState.scopes(IntSort).size
        val min = (numValues.toFloat / 2.0).ceil.toInt * -1
        val max = (numValues.toFloat / 2.0).floor.toInt - 1

        // Scopes change with the new sort
        val newScopes = problemState.scopes + (opfiSort -> ExactScope(numValues, true))

        // Create a mapping of integer values to constants
        val intToConstants: Map[Int, DomainElement] = generateConstantMapping(min, max, opfiSort)
        // And back
        val constantsToInts: Map[DomainElement, Int] = intToConstants.map({case (ival, varVal) => varVal -> ival})

        // generate interpreted functions to do casting
        val functionDefCastToInt: FunctionDefinition = FunctionDefinition(varNameGenerator.freshName(f"toInt"), Seq(ax), IntSort,
            // Generate the body by folding to make If(x == v1) then {1} else {If (x == v2) then {2} else {...  else {<any dummy value>}}}
            constantsToInts.foldLeft(IntegerLiteral(min): Term)({case (prev, (constValue, intValue)) => IfThenElse(Eq(x, constValue), IntegerLiteral(intValue), prev)})
        )
        val functionDefCastFromInt: FunctionDefinition = FunctionDefinition(varNameGenerator.freshName(f"fromInt"), Seq(x.of(IntSort)), opfiSort,
            intToConstants.foldLeft(intToConstants(min): Term)({ case (prev, (intValue, constValue)) => IfThenElse(Eq(x, IntegerLiteral(intValue)), constValue, prev)})
        )
    
        // Create an interpreted function to determine if a value is out of range
        val isOutOfBounds: FunctionDefinition = FunctionDefinition(varNameGenerator.freshName(f"outOfBoundsOPFI"), Seq(x.of(IntSort)), BoolSort,
            OrList(
                Term.mkLT(x, IntegerLiteral(min)), // x >= MIN
                Term.mkGT(x, IntegerLiteral(max)) // x <= MAX
            )
        )

        // terms setup to clear cast to/from identities
        // We don't need to cast in some cases, so this handles it
        def castToInt(term: Term): Term = term match {
            case App(functionDefCastFromInt.name, Seq(baseTerm)) => baseTerm
            case _ => App(functionDefCastToInt.name, term)
        }
        def castFromInt(term: Term): Term = term match {
            case App(functionDefCastToInt.name, Seq(baseTerm)) => baseTerm
            case _ => App(functionDefCastFromInt.name, term)
        }

        // replaces int sort while leaving other sorts unchanged
        def replaceIntSort(sort: Sort): Sort = sort match {
            case IntSort => opfiSort
            case x => x
        }

        // This is used to filter out terms that won't overflow (since we are currently casting them TO ints from an in bound constant)
        def withoutCastsToInt(terms: Seq[Term]): Seq[Term] = {
            terms.filter({
                case App(functionDefCastToInt.name, _) => false
                case _ => true
            })
        }

        // find function declarations that contain ints and therefore need to be changed
        // We store this to make casting easier later
        val (intFuncDecls, otherFuncDecls) = problemState.theory.functionDeclarations.partition(decl => decl.argSorts.contains(IntSort) || decl.resultSort == IntSort)
        // Cast the integer functions to opfiInts
        val opfiIntFuncDecls = intFuncDecls.map({
            case FuncDecl(name, argSorts, resultSort) =>
                FuncDecl(name, argSorts map replaceIntSort, replaceIntSort(resultSort))
        })

        // TODO cast arguments in function decls

        // TODO cast, add args, and transform defns

        // TODO treat constants as defns with no args

        /**
         * Any arguments to a function that are OPFI ints are currently ints
         * We need to cast them back.
         * This function is designed to do that.
         * 
         * Returns a tuple. 
         * The first value is args all of the functions arguments properly wrapped in casts.
         * The second value is a sequence of (unwrapped) arguments that were changed, and thus need to be checked for overflows.
         */
        def castFunctionArgs() = ???

        // We need to transform the definitions, but before we can do that, we cast them so we can use
        var newConstDecls = problemState.theory.signature.constantDeclarations.map(_ match {
            case AnnotatedVar(variable, IntSort) => { 
                AnnotatedVar(variable, opfiSort)
            }
            case x => x
        })


        // Recursive transformation
        // Up information is the transformedTerm and a set of overflow checks
        def transform(term: Term, down: DownInfo): (Term, Set[Term]) = term match {
            case Var(name) => {
                // If it is an opfi term, we cast it to an integer
                val modifiedTerm = if (down.opfiVars.contains(name)){
                    castToInt(term)
                } else {
                    term
                }

                // If this is a parameter, we may not know its value
                val overflowCheck = down.parameterOverflows.get(name).toSet

                (modifiedTerm, overflowCheck)
            }
            case Not(body) => {
                // Transform the body with opposite polarity
                val (transfomedBody, check) = transform(body, down.flipPolarity)
                // Check remains the same
                (Not(transfomedBody), check)
            }

            case Distinct(arguments) => {
                val (transformedArgs, checks) = arguments.map(transform(_, down)).unzip

                // TODO simplify when possible

                (Distinct(transformedArgs), unionAll(checks))
            }

            case AndList(arguments) => {
                val termsAndChecks = arguments.map(transform(_, down))
                val (transformedArgs, checks) = termsAndChecks.unzip

                // TODO simplify when possible
                
                val flatChecks = unionAll(checks)
                if (flatChecks.isEmpty){
                    (AndList(transformedArgs), Set.empty)
                } else {
                    val anyValueUnknown = unknown(flatChecks)

                    val anyKnownFalse = OrList(
                        termsAndChecks.map({
                            case (subterm, check) => 
                                And(subterm, Not(OrList(check.toSeq)))
                        })
                    )

                    // unknown when one unknown and no known false
                    val newCheck = And(anyValueUnknown, Not(anyKnownFalse))
                    (AndList(transformedArgs), Set(newCheck))
                }
            }

            case OrList(arguments) => {
                val termsAndChecks = arguments.map(transform(_, down))
                val (transformedArgs, checks) = termsAndChecks.unzip

                // TODO simplify when possible
                
                val flatChecks = unionAll(checks)
                if (flatChecks.isEmpty){
                    (OrList(transformedArgs), Set.empty)
                } else {
                    val anyValueUnknown = unknown(flatChecks)

                    val anyKnownTrue = OrList(
                        termsAndChecks.map({
                            case (subterm, checks) => 
                                knownAndTrue(subterm, checks)
                        })
                    )

                    // unknown when one unknown and no known true
                    val newCheck = And(anyValueUnknown, Not(anyKnownTrue))
                    (OrList(transformedArgs), Set(newCheck))
                }
            }

            case IfThenElse(condition, ifTrue, ifFalse) => {
                // Transform children
                val (newCond, checkCondition) = transform(condition, down)
                val (newTrue, checkTrue) = transform(ifTrue, down)
                val (newFalse, checkFalse) = transform(ifFalse, down)

                // TODO optimize with polarity and quantification
                 
                // Overflows if condition overflows, or chosen path overflows
                val condOverflows = unknown(checkCondition)
                val trueOverflows = unknown(checkTrue)
                val falseOverflows = unknown(checkFalse)
                val newCheck = Or(condOverflows, And(newCond, trueOverflows), And(Not(newCond), falseOverflows))

                val newTerm = IfThenElse(newCond, newTrue, newFalse)
                
            
                (newTerm, Set(newCheck))
            }

            case Implication(left, right) => {
                // A => B == !A || B so left has flipped polarity
                val (transformedLeft, checkLeft) = transform(left, down.flipPolarity)
                val (transformedRight, checkRight) = transform(right, down)
                
                // TODO check with known polarity

                val newTerm = Implication(transformedLeft, transformedRight)
                val newCheck = checkLeft union checkRight

                (newTerm, newCheck)
            }

            case Iff(left, right) => {
                // Eq over booleans is essentially A & B | !A & !B
                // We have to do this because the polarity goes both ways here
                // We can't default A to be true or false if we don't know what B is
                val unfoldedTerm = Or(And(left, right), And(Not(left), Not(right)))

                // Don't redo anything if we don't have to
                transform(unfoldedTerm, down)
            }

            case Forall(quants, body) => {
                // Separate out integer variables
                val (intQuantNames, nonintQuants) = quants partitionMap (_ match {
                    case AnnotatedVar(Var(name), IntSort) =>
                        Left(name)
                    case AnnotatedVar(variable, sort) =>
                        Right(AnnotatedVar(variable, sort))
                })
                // Integer variables become opfi variables
                val intQuants = intQuantNames map (name => AnnotatedVar(Var(name),opfiSort))
                // The non-integer variables remain the same
                val newQuants = intQuants ++ nonintQuants
                val newDown = down.quantified(intQuantNames.toSet)
                
                val (transformedBody, bodyUnknown) = transform(body, newDown)

                // Unknown if every value is unknown (This is permissive)
                val upTerms: Set[Term] = Set(Forall(newQuants, unknown(bodyUnknown)))

                // If the body is unknown, ignore it by making it true
                val newBody = knownOrTrue(transformedBody, bodyUnknown)

                (Forall(newQuants, newBody), upTerms)
            }

            case Exists(quants, body) => {
                // Separate out integer variables
                val (intQuantNames, nonintQuants) = quants partitionMap (_ match {
                    case AnnotatedVar(Var(name), IntSort) =>
                        Left(name)
                    case AnnotatedVar(variable, sort) =>
                        Right(AnnotatedVar(variable, sort))
                })
                // Integer variables become opfi variables
                val intQuants = intQuantNames map (name => AnnotatedVar(Var(name),opfiSort))
                // The non-integer variables remain the same
                val newQuants = intQuants ++ nonintQuants
                val newDown = down.quantified(intQuantNames.toSet)
                
                val (transformedBody, bodyUnknown) = transform(body, newDown)

                // Unknown if every value is unknown (This is permissive)
                val upTerms: Set[Term] = Set(Forall(newQuants, unknown(bodyUnknown)))

                // If the body is unknown, ignore it by making it false
                val newBody = knownOrFalse(transformedBody, bodyUnknown)

                (Exists(newQuants, newBody), upTerms)
            }

            case BuiltinApp(function, arguments) => {
                val newArgsAndChecks = arguments.map(transform(_, down.unknownPolarity))
                val (newArgs, argChecks) = newArgsAndChecks.unzip

                val anyArgOverflows = unionAll(argChecks)
                
                // TODO optimize for polarity

                // integer predicates can overflow if out of bounds
                /* NOTE we have decided to not handle casting int to bitvector at this point.
                The cast takes a bitwidth which could intentionally be smaller than the integer being used.
                As such, it is hard to say what would be "overflow" and what would be intended behavior.
                */
                // TODO Division by zero?
                val outOfBoundsChecks: Set[Term] = function match {
                    case _: BinaryIntegerRelation => {
                        // Add a check if any args are out of bounds
                        newArgs.map(App(isOutOfBounds.name, _)).toSet
                    }
                    case _ => {
                        Set.empty
                    }
                }

                val newTerm = BuiltinApp(function, newArgs)

                (newTerm, anyArgOverflows union outOfBoundsChecks)
            }

            case Eq(left, right) => {
                val (newLeft, overLeft) = transform(left, down.unknownPolarity)
                val (newRight, overRight) = transform(right, down.unknownPolarity)

                (Eq(newLeft, newRight), overLeft union overRight)
            }

            // Literals are known values
            case IntegerLiteral(value) => (IntegerLiteral(value), Set.empty)
            case DomainElement(index, sort) => (DomainElement(index, sort), Set.empty)
            case BitVectorLiteral(value, bitwidth) => (BitVectorLiteral(value, bitwidth), Set.empty)
            case EnumValue(name) => (EnumValue(name), Set.empty)
            case Top => (Top, Set.empty)
            case Bottom => (Bottom, Set.empty)

        }
        

        ???
    }
    

    case class DownInfo(
        polarity: Polarity,
        isQuantified: Boolean,
        parameterOverflows: Map[String, Term],
        opfiVars: Set[String], // Variables that are of the OPFI sort
    ){
        def flipPolarity(): DownInfo = copy(polarity = flip(polarity))

        def unknownPolarity(): DownInfo = copy(polarity = Indeterminate)

        def quantified(): DownInfo = copy(isQuantified = true)

        def quantified(newOpfis: Set[String]): DownInfo = 
            copy(isQuantified = true, opfiVars = opfiVars union newOpfis)
    }

    
}
