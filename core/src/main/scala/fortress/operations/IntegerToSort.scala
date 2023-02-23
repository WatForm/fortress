package fortress.operations

import fortress.msfol._
import fortress.util.Errors
import fortress.data.NameGenerator

class IntegerToSortConverter(min: Int, max: Int, newSort: Sort, nameGenerator: NameGenerator) {
    // TODO generate constant names instead? Probably better for other methodsThe fundamental operations on maps are similar to those on sets. They are summarized in the following table and fall into the following categories:
    // TODO custom name generator with a number we can specify?
    val intToConstants: Map[Int, Var] = Range(min, max+1).map(value => {
        val newName = f"_${value}_${newSort.name}"
        (value -> Var(newName))
    }).toMap

    val IntConsts = Seq(intToConstants.values)

    val constantsToInts: Map[Term, Int] = intToConstants.map(mapping => mapping._2 -> mapping._1)

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
        constantsToInts.foldLeft(IntegerLiteral(min): Term)({case (prev, (constValue, intValue)) => IfThenElse(Eq(x, constValue), IntegerLiteral(intValue), prev)})
    )

    var castFromInt: FunctionDefinition = FunctionDefinition(nameGenerator.freshName(f"castIntTo${newSort.name}"), Seq(ax), newSort,
        intToConstants.foldLeft(intToConstants(min): Term)({ case (prev, (intValue, constValue)) => IfThenElse(Eq(x, IntegerLiteral(intValue)), constValue, prev)})
    )

    private def inRange(x: Int): Boolean = {
        return (x >= min && x <= max)
    }
    
    // A map from a builtin to a definition for it
    var convertableFunctions: Map[BuiltinFunction, (FunctionDefinition)] = {
        
        // x is left value, y is right value, z is result value
        // Looks through all cases, with default
        def generateFunctionBody2(op: (Int, Int) => Int, checkDivZero: Boolean = false): Term = {
            var body: Term = intToConstants(min)
            for (left <- Range(min, max+1)) {
                for (right <- Range(min, max+1)) {
                    if (checkDivZero && right == 0){
                        // skip because div by zero should be an overlfow
                    } else {
                        val result = op(left, right)
                        if (inRange(result)){
                            body = IfThenElse(And(Eq(x, intToConstants(left)), Eq(y, intToConstants(right))), intToConstants(result), body)
                        }
                    }
                }
            }
            body
        }
        // TODO clean this up somehow? Make the interpreted function cleaner?
        // Could we just use the cast to int for comparisons?
        // x is left value, y is right value
        def generateComparisonBody(op: (Int,Int) => Boolean): Term = {
            var body: Term = Bottom // default to false?
            for (left <- Range(min, max+1)){
                for (right <- Range(min, max+1)){
                    val result =  if (op(left, right)) {Top} else {Bottom}
                    // if x and y are what we checked, then it's the proper result.
                    body = IfThenElse(And(Eq(x, intToConstants(left)), Eq(y, intToConstants(right))), result, body)
                }
            }
            body
        }

        def generateFunctionDefinition2(nameBase: String, op: (Int, Int) => Int, checkDivZero: Boolean = false): FunctionDefinition = {
            FunctionDefinition(nameGenerator.freshName(nameBase), axy, newSort, generateFunctionBody2(op, checkDivZero))
        }
        Map[BuiltinFunction, FunctionDefinition](
            IntPlus -> generateFunctionDefinition2("+", _+_),
            IntSub -> generateFunctionDefinition2("-", _-_),
            IntMult -> generateFunctionDefinition2("*", _*_),
            IntDiv -> generateFunctionDefinition2("/", _/_, true),
            // TODO MORE
        )
    }
    // A function to create a function declaration for a version of the builtin function using the new sort
    def createFuncDecl(func: BuiltinFunction): FuncDecl = {
        ???
    }
    // The term is the new term, the boolean is true if we have done a substitution
    class IntegerToSortVisitor extends TermVisitor[(Term, Boolean)] {

        override def visitTop(): (Term, Boolean) = (Top, false)

        override def visitBottom(): (Term, Boolean) = (Bottom, false)

        override def visitVar(term: Var): (Term, Boolean) = (term, false)

        override def visitEnumValue(term: EnumValue): (Term, Boolean) = (term, false)

        override def visitDomainElement(term: DomainElement): (Term, Boolean) = (term, false)

        override def visitNot(term: Not): (Term, Boolean) = {
            // Substitute into the body
            val (newBody, substituted) = visit(term.body)
            (Not(newBody), substituted)
        }

        def visitAndList(term: AndList) = {
            // Substitute each of the bodies
            val (newBodies, substituted) = term.arguments.map(visit).unzip
            // do we want to raise substituted? We are now
            val didSub = substituted.exists(x => x) // Just looks for one that is true
            (AndList(newBodies), didSub)
        }

        override def visitOrList(term: OrList): (Term, Boolean) = {
            // Substitute each of the bodies
            val (newBodies, substituted) = term.arguments.map(visit).unzip
            // do we want to raise substituted? We are now
            val didSub = substituted.exists(x => x) // Just looks for one that is true
            (OrList(newBodies), didSub)
        }

        override def visitDistinct(term: Distinct): (Term, Boolean) = {
            // Substitute each of the bodies
            val (newBodies, substituted) = term.arguments.map(visit).unzip
            // do we want to raise substituted? We are now
            val didSub = substituted.exists(x => x) // Just looks for one that is true
            (Distinct(newBodies), didSub)
        }

        override def visitImplication(term: Implication): (Term, Boolean) = {
            val (newLeft, subLeft) = visit(term.left)
            val (newRight, subRight) = visit(term.right)
            (Implication(newLeft, newRight), subLeft || subRight)
        }

        override def visitIff(term: Iff): (Term, Boolean) = {
            val (newLeft, subLeft) = visit(term.left)
            val (newRight, subRight) = visit(term.right)
            (Iff(newLeft, newRight), subLeft || subRight)
        }

        override def visitEq(term: Eq): (Term, Boolean) = {
            val (newLeft, subLeft) = visit(term.left)
            val (newRight, subRight) = visit(term.right)
            (Eq(newLeft, newRight), subLeft || subRight)
        }

        override def visitApp(term: App): (Term, Boolean) = {
            // Functions need to be type-changed ahead of time
            val (arguments, substituted) = term.arguments.map(visit).unzip
            val anySubstituted = substituted.exists(x => x)
            (App(term.functionName, arguments), anySubstituted)
        }

        override def visitBuiltinApp(term: BuiltinApp): (Term, Boolean) = {
            // Substitute internals
            val (newArgs, argsSubstituted) = term.arguments.map(visit).unzip
            val anyArgSubstituted = argsSubstituted.exists(x => x)

            // If already defined, just do that
            convertedFunctions.get(term.function) match {
                case Some(newFunctionDef) => return (App(newFunctionDef.name, newArgs), true)
                case None => None
            }

            // Check if we redefine the function
            if (convertableFunctions isDefinedAt term.function) {
                var newDecl = createFuncDecl(term.function)
                (App(newDecl.name, newArgs), true)
            } else {
                // Do not convert
                (BuiltinApp(term.function, newArgs), anyArgSubstituted)
            }


        }

        override def visitExists(term: Exists): (Term, Boolean) = {
            var changedTypes = false
            val newVars = term.vars.map(_ match {
                case AnnotatedVar(v, IntSort) => {
                    changedTypes = true
                    AnnotatedVar(v, newSort)
                }
                case avar => avar
            })
            var (newBody, substitutedBody) = visit(term.body)
            (Exists(newVars, newBody), changedTypes || substitutedBody)
        }

        override def visitForall(term: Forall): (Term, Boolean) = {
            var changedTypes = false
            val newVars = term.vars.map(_ match {
                case AnnotatedVar(v, IntSort) => {
                    changedTypes = true
                    AnnotatedVar(v, newSort)
                }
                case avar => avar
            })
            var (newBody, substitutedBody) = visit(term.body)
            (Forall(newVars, newBody), changedTypes || substitutedBody)
        }

        override def visitIntegerLiteral(term: IntegerLiteral): (Term, Boolean) = (intToConstants(term.value), true)

        override def visitBitVectorLiteral(term: BitVectorLiteral): (Term, Boolean) = (term, false)

        override def visitIfThenElse(term: IfThenElse): (Term, Boolean) = {
            val (newConditional, substitutedConditional) = visit(term.condition)
            val (newIfTrue, substitutedTrue) = visit(term.ifTrue)
            val (newIfFalse, substitutedFalse) = visit(term.ifFalse)
            val substituted = substitutedConditional || substitutedTrue || substitutedFalse
            (IfThenElse(newConditional, newIfTrue, newIfFalse), substituted)
        }

        override def visitClosure(term: Closure): (Term, Boolean) = {
            // Substitute each of the bodies
            val (newArguments, substituted) = term.allArguments.map(visit).unzip
            // do we want to raise substituted? We are now
            val didSub = substituted.exists(x => x) // Just looks for one that is true
            (Term.mkClosure(term.functionName, newArguments), didSub)
        }

        override def visitReflexiveClosure(term: ReflexiveClosure): (Term, Boolean) = {
            // Substitute each of the bodies
            val (newArguments, substituted) = term.allArguments.map(visit).unzip
            // do we want to raise substituted? We are now
            val didSub = substituted.exists(x => x) // Just looks for one that is true
            (Term.mkClosure(term.functionName, newArguments), didSub)
        }

        
    }
}