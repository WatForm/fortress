package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.util.Errors
import fortress.util.IntegerSize._
import fortress.util.Extensions.IntExtension
import java.lang.IllegalArgumentException
import java.util.ArrayList
import fortress.operations.TheoryOps._
import fortress.operations.TermOps._

import scala.jdk.CollectionConverters._
import scala.util.Using
import fortress.problemstate.ProblemState
import fortress.operations.RecursiveAccumulator

class NoOverflowBVTransformer extends ProblemStateTransformer (){


// TODO check going up from univ  should not default to counting as univ anymore?
  def apply(problemState: ProblemState): ProblemState = {
    val oldTheory = problemState.theory

    // Run through definitions to get their overflows
    val defOverflows: scala.collection.mutable.Map[String, ResultInfo] = scala.collection.mutable.Map.empty


    var newSig = oldTheory.signature
    // We eliminate definitions with predicates in them, so we can determine which are univ/ext later
    // We just keep them in the upinfo for ease of use
    for (defn <- newSig.definitionsInDependencyOrder){
      defn match {
        case Left(cdef) => {
          newSig = newSig.withoutConstantDefinition(cdef)
          val result = fixOverflow(cdef.body, newSig, defOverflows = defOverflows.toMap)
          // the new definition uses the results cleaned term
          newSig = newSig.withConstantDefinition(cdef.copy(body=result.cleanTerm))
          defOverflows.addOne(cdef.name -> result)
        }
        case Right(fDef) => {
          newSig = newSig.withoutFunctionDefinition(fDef)
          
          val sigWithArgs = newSig.withConstantDeclarations(fDef.argSortedVar)
          val result = fixOverflow(fDef.body, sigWithArgs, defOverflows = defOverflows.toMap)
          newSig = newSig.withFunctionDefinition(fDef.copy(body=result.cleanTerm)) 
        }
      }
    }
    
    
    val newAxioms = oldTheory.axioms.map(fixOverflow(_, newSig, defOverflows = defOverflows.toMap).cleanTerm)
    val newTheory = oldTheory.withoutAxioms.withAxioms(newAxioms)

    problemState.withTheory(newTheory)
  }

    case class ResultInfo(cleanTerm: Term, univChecks: Set[Term], extChecks: Set[Term], containsUnivVar: Boolean){
        // Combines two results into a sequence of subterms, unions the checks and contains a univVar if anysubterm does
        def +(other: ResultInfo): (Seq[Term], Set[Term], Set[Term], Boolean) = (
          (Seq(cleanTerm, other.cleanTerm),
           univChecks | other.univChecks,
           extChecks | other.extChecks,
           containsUnivVar | other.containsUnivVar
          )
        )

        def combine(op: (Term, Term) => Term): (ResultInfo => ResultInfo) = {
          def combinator(other: ResultInfo) = {
            val (_, univChecks, extChecks, containsUnivVar) = this + other
            ResultInfo(
              op(cleanTerm, other.cleanTerm),
              univChecks | other.univChecks,
              extChecks | other.extChecks,
              containsUnivVar || other.containsUnivVar
            )
          }
          combinator
        }

        def mapTerm(op: Term => Term): ResultInfo = {
          ResultInfo(op(cleanTerm), univChecks, extChecks, containsUnivVar)
        }

        def replaceTerm(newTerm: Term): ResultInfo = {
          ResultInfo(newTerm, univChecks, extChecks, containsUnivVar)
        }

        def withoutVars(vars: Set[Var]): ResultInfo = {
          // Remove all checks that contain the given variables
          val newUnivChecks = univChecks.filter(check => (check.freeVarConstSymbols intersect vars).isEmpty)
          val newExtChecks = extChecks.filter(check => (check.freeVarConstSymbols intersect vars).isEmpty)

          copy(univChecks = newUnivChecks, extChecks = newExtChecks)
        }

        // helper for quantifiers
        def withoutVars(vars: Seq[AnnotatedVar]): ResultInfo = {
          withoutVars(vars.map(_.variable).toSet)
        }

        def substituteChecks(subs: Map[Var, Term], univVars: Set[Var]): ResultInfo = {
          val allChecks = (extChecks.map(_.fastSubstitute(subs)) union univChecks.map(_.fastSubstitute(subs)))
          val (newExt, newUniv) = allChecks.partition(RecursiveAccumulator.freeVariablesIn(_).intersect(univVars).isEmpty)
          copy(
            extChecks = newExt,
            univChecks = newUniv  
          )
        }
    }

    def combineResults(infos: Seq[ResultInfo]): (Seq[Term], Set[Term], Set[Term], Boolean) = {
      val cleanSubterms: Seq[Term] = infos.map(_.cleanTerm)
      val univChecks: Set[Term] = infos.map(_.univChecks).fold(Set.empty)(_ union _)
      val extChecks: Set[Term] = infos.map(_.extChecks).fold(Set.empty)(_ union _)
      val containsUnivVar = infos.map(_.containsUnivVar).contains(true) // big or
      return (cleanSubterms, univChecks, extChecks, containsUnivVar)
    }

    def combineResults(infos: Seq[ResultInfo], termCombiner: Seq[Term] => Term): ResultInfo = {
      val (cleanSubterms, univChecks, extChecks, containsUnivVar) = combineResults(infos)
      val newTerm = termCombiner(cleanSubterms)
      return ResultInfo(newTerm, univChecks, extChecks, containsUnivVar)
    }

    // Skipping If then Else because it can be different types
    // How does this interact with
    // Change terms that can overflow into overflow checks. Separate them into contains ext or not
    /**
      * 
      *
      * @param term The term being cleaned
      * @param sig The current signature
      * @param polarity The current polarity (Should be initially true, negations will flip it)
      * @param univVars Set of universally quantified vars
      * @param extVars Set of existentially quantified vars
      * @param defOverflows (clean term is meaningless) overflow information for constant and function definitions
      * @return (cleanTerm, Overflow checks for subexpressions with a universally quantified var, Overflow checks for other subexpressions )
      */
    def fixOverflow(term: Term, sig: Signature, polarity: Boolean = true, univVars: Set[Var] = Set.empty, extVars: Set[Var] = Set.empty, defOverflows: Map[String, ResultInfo]): ResultInfo = term match {
      case Var(x) => {
        if (defOverflows isDefinedAt x){
          // We use the overflows from the constant Definition
          // Everything in the def is either Ext. Quantified or the quantifier is already in the body
          defOverflows(x).copy(cleanTerm = Var(x), containsUnivVar = false)
        } else {
          ResultInfo(Var(x), Set.empty, Set.empty, univVars.contains(Var(x)))
        }
      }
      case _: LeafTerm => ResultInfo(term, Set.empty, Set.empty, false)

      // Integer predicates (The +,-,etc are BitVectorFunctions)
      case BuiltinApp(function : BinaryBitVectorRelation, arguments) => {
        val left = arguments(0)
        val right = arguments(1)
        val resLeft = fixOverflow(left, sig, polarity, univVars, extVars, defOverflows)
        val resRight = fixOverflow(right, sig, polarity, univVars, extVars, defOverflows)
        val op: (Term, Term) => Term = (a: Term, b: Term) => BuiltinApp(function, Seq(a, b))
        val resCombined = resLeft.combine(op)(resRight)
        
        applyChecks(resCombined, polarity)
      }

      // TODO change to have predicates 
      case BuiltinApp(function, arguments) => {
          // clean up arguments and get their checks
          val (cleanArgs, univChecks, extChecks, containsUnivVar) = combineResults(arguments.map(fixOverflow(_, sig, polarity, univVars, extVars, defOverflows)))
          val newTerm = BuiltinApp(function, cleanArgs)
          // include this term if it can overflow
          val allOverflowTerms = if (canOverflow(term)) {
            val newChecks = overflowCheck(newTerm, sig).get
            // Place it in the correct set based on if we have a univVar or not
            if(containsUnivVar){
              return ResultInfo(newTerm, univChecks.incl(newChecks), extChecks, containsUnivVar)
            } else {
              return ResultInfo(newTerm, univChecks, extChecks.incl(newChecks), containsUnivVar)
            }
          } 
          // Else we return the cleaned term
          return ResultInfo(newTerm, univChecks, extChecks, containsUnivVar)
      }

      case Forall(vars, body) => {
        // put vars into new sig
        val newSig = sig.withConstantDeclarations(vars)
        val newUnivVars = univVars.++(vars.map(_.variable))
        val bodyInfo = fixOverflow(body, newSig, polarity, newUnivVars, extVars, defOverflows)
        
        return bodyInfo.mapTerm(Forall(vars, _)).withoutVars(vars)
      }

      case Exists(vars, body) => {
        // put vars into new sig
        val newSig = sig.withConstantDeclarations(vars)
        val newUnivVars = univVars.++(vars.map(_.variable))
        val bodyInfo = fixOverflow(body, newSig, polarity, newUnivVars, extVars, defOverflows)
        return bodyInfo.mapTerm(Exists(vars, _)).withoutVars(vars)
      }

      // todo closure and no overflow semantics? Closure not allowed quantifiers, but it could have operators...
      // just check if overflow in arguments?
      case Closure(functionName, arg1, arg2, fixedArgs) => {
        val res1 = fixOverflow(arg1, sig, polarity, univVars, extVars, defOverflows)
        val res2 = fixOverflow(arg2, sig, polarity, univVars, extVars, defOverflows)
        val (cleanFixed, fixedUnivChecks, fixedExtChecks, fixedUnivVar) = combineResults(fixedArgs.map(fixOverflow(_, sig, polarity, univVars, extVars, defOverflows)))
        val univChecks = res1.univChecks | res2.univChecks | fixedUnivChecks
        val extChecks = res1.extChecks | res2.extChecks | fixedExtChecks
        val containsUnivVar = res1.containsUnivVar || res2.containsUnivVar || fixedUnivVar
        ResultInfo(Closure(functionName, res1.cleanTerm, res2.cleanTerm, cleanFixed), univChecks, extChecks, containsUnivVar)
      }
      case ReflexiveClosure(functionName, arg1, arg2, fixedArgs) => {
        val res1 = fixOverflow(arg1, sig, polarity, univVars, extVars, defOverflows)
        val res2 = fixOverflow(arg2, sig, polarity, univVars, extVars, defOverflows)
        val (cleanFixed, fixedUnivChecks, fixedExtChecks, fixedUnivVar) = combineResults(fixedArgs.map(fixOverflow(_, sig, polarity, univVars, extVars, defOverflows)))
        val univChecks = res1.univChecks | res2.univChecks | fixedUnivChecks
        val extChecks = res1.extChecks | res2.extChecks | fixedExtChecks
        val containsUnivVar = res1.containsUnivVar || res2.containsUnivVar || fixedUnivVar
        ResultInfo(ReflexiveClosure(functionName, res1.cleanTerm, res2.cleanTerm, cleanFixed), univChecks, extChecks, containsUnivVar)
      }

      // TODO EQ
      case Eq(left, right) => {
        val sort = left.typeCheck(sig).sort

        sort match {
          case BoolSort => {
            val resPosLeft = fixOverflow(left, sig, polarity, univVars, extVars, defOverflows)
            val resPosRight = fixOverflow(right, sig, polarity, univVars, extVars, defOverflows)
            val resNegLeft = fixOverflow(left, sig, !polarity, univVars, extVars, defOverflows)
            val resNegRight = fixOverflow(right, sig, !polarity, univVars, extVars, defOverflows)
            
            // A == B    is A&B |!A&!B so for proper polarity
            val resPos = resPosLeft.combine(And(_,_))(resPosRight)
            val resNeg = resNegLeft.combine((a,b) =>And(Not(a), Not(b)))(resNegRight) // the a and b are for weird scala behavior
            val resCombined = resPos.combine(Or(_,_))(resNeg)

            //val resCombined =  resLeft.combine(Iff(_, _))(resRight)
          
            // If uncaught overflows, check
            if (!resCombined.univChecks.isEmpty || !resCombined.extChecks.isEmpty){
              applyChecks(resCombined, polarity)
            } else {
              resCombined
            }
          }

          case _ => {
            // This is a predicate, potentially an integer predicate
            val resLeft = fixOverflow(left, sig, polarity, univVars, extVars, defOverflows)
            val resRight = fixOverflow(right, sig, polarity, univVars, extVars, defOverflows)
            val resCombined = resLeft.combine((a,b) => Eq(a, b))(resRight)

            // If uncaught overflows, check
            if (!resCombined.univChecks.isEmpty || !resCombined.extChecks.isEmpty){
              applyChecks(resCombined, polarity)
            } else {
              resCombined
            }
          }
        }
        

        
      }


      case Iff(left, right) => {
        val resPosLeft = fixOverflow(left, sig, polarity, univVars, extVars, defOverflows)
        val resPosRight = fixOverflow(right, sig, polarity, univVars, extVars, defOverflows)
        val resNegLeft = fixOverflow(left, sig, !polarity, univVars, extVars, defOverflows)
        val resNegRight = fixOverflow(right, sig, !polarity, univVars, extVars, defOverflows)
        
        // A <==> B    is A&B |!A&!B so for proper polarity
        val resPos = resPosLeft.combine(And(_,_))(resPosRight)
        val resNeg = resNegLeft.combine((a,b) =>And(Not(a), Not(b)))(resNegRight) // the a and b are for weird scala behavior
        val resCombined = resPos.combine(Or(_,_))(resNeg)

        //val resCombined =  resLeft.combine(Iff(_, _))(resRight)
      
        // If uncaught overflows, check
        if (!resCombined.univChecks.isEmpty || !resCombined.extChecks.isEmpty){
          applyChecks(resCombined, polarity)
        } else {
          resCombined
        }
      }

      case Implication(left, right) => {
        val resLeft = fixOverflow(left, sig, !polarity, univVars, extVars, defOverflows)
        val resRight = fixOverflow(right, sig, polarity, univVars, extVars, defOverflows)
        return resLeft.combine(Implication(_, _))(resRight)
      }

      case Not(body) => {
        val result = fixOverflow(body, sig, !polarity, univVars, extVars, defOverflows)
        result.mapTerm(Not(_))
      }

      case AndList(arguments) => {
        val (cleanArgs, univChecks, extChecks, containsUnivVar) = combineResults(arguments.map(fixOverflow(_, sig, polarity, univVars, extVars, defOverflows)))
        ResultInfo(AndList(cleanArgs), univChecks, extChecks, containsUnivVar)
      }
      case OrList(arguments) => {
        val (cleanArgs, univChecks, extChecks, containsUnivVar) = combineResults(arguments.map(fixOverflow(_, sig, polarity, univVars, extVars, defOverflows)))
        ResultInfo(OrList(cleanArgs), univChecks, extChecks, containsUnivVar)
      }

      
      case App(functionName, arguments) => {
        // Clean up all the arguments
        val (cleanArgs, univChecks, extChecks, containsUnivVar) = combineResults(arguments.map(fixOverflow(_, sig, polarity, univVars, extVars, defOverflows)))
        val combinedArgInfo = ResultInfo(App(functionName, cleanArgs), univChecks, extChecks, containsUnivVar)

        var allInfo = combinedArgInfo
        if (defOverflows isDefinedAt functionName){
          // Include checks from the body
          val argNames = sig.queryFunctionDefinition(functionName).get.argSortedVar.map(_.variable)
          val substitutions = argNames.zip(arguments).toMap
          val bodyInfo = defOverflows(functionName).substituteChecks(substitutions, univVars)

          allInfo = ResultInfo(
            combinedArgInfo.cleanTerm,
            combinedArgInfo.univChecks | bodyInfo.univChecks,
            combinedArgInfo.extChecks | bodyInfo.extChecks,
            combinedArgInfo.containsUnivVar
            )
        }
        // Non-predicate, no check needed. Predicate, add checks
        if (isPredicate(functionName, sig)){
          applyChecks(allInfo, polarity)
        } else {
          allInfo
        }
      }

      // Distinct is a predicate, so we need checks!
      case Distinct(arguments) => {
        val (cleanArgs, univChecks, extChecks, containsUnivVar) = combineResults(arguments.map(fixOverflow(_, sig, polarity, univVars, extVars, defOverflows)))
        val combined = ResultInfo(Distinct(cleanArgs), univChecks, extChecks, containsUnivVar)
        applyChecks(combined, polarity)
      }

      // TODO check ITE conditioning?
      /*
      // ITE will just give itself as something that can overflow?
      // For now we just say any overflow is an overflow
      case IfThenElse(condition, ifTrue, ifFalse) => {
        val (cleanCondition, overflowablesCondition) = fixOverflow(condition, sig)
        val (cleanTrue, overflowablesTrue) = fixOverflow(ifTrue, sig)
        val (cleanFalse, overflowablesFalse) = fixOverflow(ifFalse, sig)

        val cleanITE = IfThenElse(cleanCondition, cleanTrue, cleanFalse)
        // TODO change to only overflow in the selected branch
        val overflows = overflowablesCondition | overflowablesTrue | overflowablesFalse
        return (cleanITE, overflows)
      }
      */
      /* If (C) T else E === C & T | !C & E
       * So This lazily does overflows for T and E (just do the normal recursive handling)
       * condition's Issues should be applied to ITE if it can overflow?
       */
      case IfThenElse(condition, ifTrue, ifFalse) => {
        val conditionResult = fixOverflow(condition, sig, defOverflows = defOverflows)
        val ifTrueResult = fixOverflow(ifTrue, sig, defOverflows = defOverflows)
        val ifFalseResult = fixOverflow(ifFalse, sig, defOverflows = defOverflows)

        // up Does not overflow when all of its overflows are false
        val conditionOverflows = conditionResult.extChecks.toSeq ++ conditionResult.univChecks.toSeq
        val upDoesNotOverflow = if (conditionOverflows.isEmpty) {Top} else {Not(OrList(conditionOverflows))}

        // NOTE what if left branch has univ but we take the right branch and that overflows (above the ITE) it should be treated existentially
        // branches only cause an overflow if we actually use the value
        val overflowUniv = AndList(upDoesNotOverflow,
          IfThenElse(conditionResult.cleanTerm,
            orDefaultFalse(ifTrueResult.univChecks.toSeq),
            orDefaultFalse(ifFalseResult.univChecks.toSeq),
          )
        )
        val overflowExt = AndList(upDoesNotOverflow,
          IfThenElse(conditionResult.cleanTerm,
            orDefaultFalse(ifTrueResult.extChecks.toSeq),
            orDefaultFalse(ifFalseResult.extChecks.toSeq),
          )
        )
        

        val univChecks = conditionResult.univChecks + overflowUniv
        val extChecks = conditionResult.extChecks + overflowExt

        val containsUnivVar = conditionResult.containsUnivVar || ifTrueResult.containsUnivVar || ifFalseResult.containsUnivVar

        val cleanedTerm = IfThenElse(conditionResult.cleanTerm, ifTrueResult.cleanTerm, ifFalseResult.cleanTerm)

        ResultInfo(cleanedTerm, univChecks, extChecks, containsUnivVar)
        
        /*
        val cleanedInside = IfThenElse(conditionResult.cleanTerm, ifTrueResult.cleanTerm, ifFalseResult.cleanTerm)

        // Make checks just for condition on outside
        val uncheckedResult = conditionResult.replaceTerm(cleanedInside)
        val cleanedConditionResult = applyChecks(uncheckedResult, polarity)
        val cleanedTerm = cleanedConditionResult.cleanTerm

        // New checks for overflow:
        // Anything from C
        // C & OR(anything from T), !C & (anything from E)
        val trueExtChecks = AndList(conditionResult.cleanTerm, OrList(ifTrueResult.extChecks.toSeq))
        val trueUnivChecks = AndList(conditionResult.cleanTerm, OrList(ifTrueResult.univChecks.toSeq))

        val falseExtChecks = AndList(conditionResult.cleanTerm, OrList(ifFalseResult.extChecks.toSeq))
        val falseUnivChecks = AndList(conditionResult.cleanTerm, OrList(ifFalseResult.univChecks.toSeq))
        
        val univChecks = cleanedConditionResult.univChecks + trueUnivChecks + falseUnivChecks
        val extChecks = cleanedConditionResult.extChecks + trueExtChecks + falseExtChecks

        val containsUnivVar = conditionResult.containsUnivVar || ifTrueResult.containsUnivVar || ifFalseResult.containsUnivVar

        ResultInfo(cleanedTerm, univChecks, extChecks, containsUnivVar)
        */
      }
    }
    

    def orDefaultFalse(args: Seq[Term]): Term = {
      if (args.isEmpty){
        Bottom
      } else if (args.size == 1){
        args(0)
      } else {
        OrList(args)
      }
    }
    def isPredicate(functionName: String, sig: Signature): Boolean = {
      sig.queryFunction(functionName) match {
        case None => Errors.Internal.impossibleState("Trying to check if function '" + functionName + "' is a predicate, but it is not in the signature.")
        case Some(Left(fdecl)) => fdecl.resultSort == BoolSort
        case Some(Right(fdef)) => fdef.resultSort == BoolSort
      }
    }

    /**
      * Applies the checks in `currentInfo` to "hide" overflows. 
      * Keeps checks so they can be applied again if another comparison is used
      * @param currentInfo
      * @param polarity
      * @return
      */
    def applyChecksOld(currentInfo: ResultInfo, polarity: Boolean): ResultInfo = {
      // bdef = no existentials or all existentials are defined
      // so bdef = all existential checks are false (so no existentials overflow)
        val bDef: Term = if (currentInfo.extChecks.isEmpty) {
          Top
        } else if (currentInfo.extChecks.size == 1){
          currentInfo.extChecks.toSeq.map(Not(_))(0)
        } else {
          // TODO make this more efficient by 
          val definedChecks = currentInfo.extChecks.toSeq.map(Not(_))
          AndList(definedChecks)
        }
          
        // bundef = some universals and any univ is undefined
        val bUndef = if (currentInfo.univChecks.size == 1){
          currentInfo.univChecks.toSeq(0)
        } else if (currentInfo.containsUnivVar) {
          OrList(currentInfo.univChecks.toSeq)
        } else {
          Bottom
        }

        val b = currentInfo.cleanTerm

        val cleanTerm = if (polarity){
          // (b | bUndef) & bDef
          (bDef, bUndef) match {
            case (Top, Bottom) =>  b
            case (Top, _) => Or(b, bUndef)
            case (_, Bottom) => And(b, bDef)
            case (_, _) => And(Or(b, bUndef), bDef)
          }
        } else {
          (bDef, bUndef) match {
            // todo cleanup negation for nnf
            // (b | !bDef) & !bUndef
            case (Top, Bottom) => b
            case (Top, _) => And(b, Not(bUndef))
            case (_, Bottom) => Or(b, Not(bDef))
            case (_, _) => And(Or(b, bUndef), bDef)
          }
        }

        // Not sure if containsUnivVar should be reset here.
        // Pretty sure no
        currentInfo.replaceTerm(cleanTerm)
    }

    /**
      * Applies the checks in `currentInfo` to "hide" overflows. 
      * Keeps checks so they can be applied again if another comparison is used
      * @param currentInfo
      * @param polarity
      * @return
      */
    def applyChecks(currentInfo: ResultInfo, polarity: Boolean): ResultInfo = {
      // Positive: (Term or Univ overflows) and Ext does not overflow
      // Negative (Term or Ext overflows) and Univ does not overflow

      // Simplify checks to a disjunction of all of them. We default to no overflow occuring
      val univOverflows: Term = currentInfo.univChecks.size match {
        case 0 => Bottom
        case 1 => currentInfo.univChecks.head
        case _ => OrList(currentInfo.univChecks.toSeq)
      }
      val extOverflows = currentInfo.extChecks.size match {
        case 0 => Bottom
        case 1 => currentInfo.extChecks.head
        case _ => OrList(currentInfo.extChecks.toSeq)
      }

      val unguardedTerm = currentInfo.cleanTerm
      val cleanTerm = if (polarity){
        (univOverflows, extOverflows) match {
          case (Bottom, Bottom) => unguardedTerm
          case (Bottom, _) => And(unguardedTerm, Not(extOverflows))
          case (_, Bottom) => Or(unguardedTerm, univOverflows)
          case _ => And(Or(unguardedTerm, univOverflows), Not(extOverflows))
        }
      } else {
        (univOverflows, extOverflows) match {
          case (Bottom, Bottom) => unguardedTerm
          case (Bottom, _) => Or(unguardedTerm, extOverflows)
          case (_, Bottom) => And(unguardedTerm, Not(univOverflows))
          case _ => And(Or(unguardedTerm, extOverflows), Not(univOverflows))
        }
      }

      currentInfo.replaceTerm(cleanTerm)
    }

    def canOverflow(term: Term): Boolean = term match {
      case BuiltinApp(function, arguments) => function match {
        case BvNeg => true
        // These need some double checking
        case BvPlus => true
        // Negate and check for addition
        case BvSub => true
        // Division will over/underflow with divide by zero
        case BvSignedDiv => true
        case BvSignedMod => true
        case BvSignedRem => true
        // multiply will not overflow buffers of double width.
        // Do the multiplication and check
        case BvMult => true
        case _ => false
      }

      case _ => false
    }

    def bvSubtoPlus(term :Term): Term = term match {
      case BuiltinApp(BvSub, Seq(x, y)) => BuiltinApp(BvPlus, x, BuiltinApp(BvNeg, y))
      case _ => Errors.Internal.impossibleState(term.toString() + " is not an app of BvSub!")
    }
    def bvSubtoPlus(args: Seq[Term]): Term = args match {
      case Seq(x, y) => BuiltinApp(BvPlus, x, BuiltinApp(BvNeg, y))
      case _ => Errors.Internal.impossibleState("Bad arguments for BvSub!")
    }

    // Adds a check to ensure a division does not divide by zero
    def checkDivideByZero(arguments: Seq[Term], signature: Signature): Term = {
      Errors.Internal.precondition(arguments.length == 2)
      val denominator = arguments(1)
      val bitwidth = bitvectorWidth(denominator, signature).get
      val zero = BitVectorLiteral(0, bitwidth)
      return Eq(denominator, zero)
    }

    /**
      * Gets a term that will evaluate to true when `term` would overflow.
      *
      * @param term
      * @param signature
      * @return A `Term` that will evaluate to true when `term` would cause an overflow.
      */
    def overflowCheck(term: Term, signature: Signature): Option[Term] = term match {
      case BuiltinApp(function, arguments) => function match {
        case BvNeg => {
          // Overflow occurs when the value negated is the minimum value
          val body: Term = arguments(0)
          val bitwidth = bitvectorWidth(body, signature).get
          val minBV = BitVectorLiteral(minimumIntValue(bitwidth), bitwidth)
          return Some(Eq(body, minBV))
        }
        // These need some double checking
        case BvPlus => {
          // Overflow will occur if signs of operands are the same, but result changes sign
          val x = arguments(0)
          val y = arguments(1)
          val bitwidth = bitvectorWidth(x, signature).get
          val zero = BitVectorLiteral(0, bitwidth)
          // (x > 0) & (y > 0) => (x + y > 0)
          // So overflow if (x > 0) & (y > 0) & !(x + y > 0)
          // and underflow if (x < 0) & (y < 0) & !(x + y < 0_
          return Some(Or(
            And(
              BuiltinApp(BvSignedGT, x, zero), 
              BuiltinApp(BvSignedGT, y, zero),
              Not(BuiltinApp(BvSignedGT, BuiltinApp(BvPlus, x, y), zero))
            ),
            And(
              BuiltinApp(BvSignedLT, x, zero), 
              BuiltinApp(BvSignedLT, y, zero),
              Not(BuiltinApp(BvSignedLT, BuiltinApp(BvPlus, x, y), zero))
            )
          ))
        }
        // Negate and check for addition, check both for overflow
        case BvSub => {
          Some(Or(overflowCheck(bvSubtoPlus(term), signature).get, overflowCheck(BuiltinApp(BvNeg, arguments(1)), signature).get))
        }
        // Division will over/underflow with divide by zero
        case BvSignedDiv | BvSignedMod | BvSignedRem => Some(checkDivideByZero(arguments, signature))
        // multiply will not overflow buffers of double width.
        // Do the multiplication and check
        case BvMult => {
          val x = arguments(0)
          val y = arguments(1)
          val bitwidth = bitvectorWidth(x, signature).get
          val doubleWidth = bitwidth * 2
          val smallMin = BitVectorLiteral(minimumIntValue(bitwidth), doubleWidth)
          val smallMax = BitVectorLiteral(maximumIntValue(bitwidth), doubleWidth)
          val padding = BitVectorLiteral(0, bitwidth)

          val bigX = BuiltinApp(BvConcat, padding, x)
          val bigY = BuiltinApp(BvConcat, padding, y)
          
          val multResult = BuiltinApp(BvMult, bigX, bigY)
          // Check result is not out of bounds!
          val underflow = BuiltinApp(BvSignedLT, multResult, smallMin)
          val overflow = BuiltinApp(BvSignedGT, multResult, smallMax)

          Some(Or(underflow, overflow))
        }
        case _ => None
      }
      case _ => None
    }
}

object NoOverflowBVTransformer extends NoOverflowBVTransformer {}