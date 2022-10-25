package fortress.transformers

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.util.Errors
import fortress.util.IntegerSize._
import fortress.util.Extensions.IntExtension
import java.lang.IllegalArgumentException
import java.util.ArrayList
import fortress.operations.TheoryOps._

import scala.jdk.CollectionConverters._
import scala.util.Using

class NoOverflowBVTransformer extends ProblemStateTransformer (){

  def name = "NoOverflowBVTransformer"

  def apply(problemState: ProblemState): ProblemState = {
    val oldTheory = problemState.theory
    
    
    val newAxioms = oldTheory.axioms.map(fixOverflow(_, oldTheory.signature).cleanTerm)
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
      * @return (cleanTerm, Overflow checks for subexpressions with a universally quantified var, Overflow checks for other subexpressions )
      */
    def fixOverflow(term: Term, sig: Signature, polarity: Boolean = true, univVars: Set[Var] = Set.empty, extVars: Set[Var] = Set.empty): ResultInfo = term match {
      case Var(x) => ResultInfo(Var(x), Set.empty, Set.empty, univVars.contains(Var(x)))
      case _: LeafTerm => ResultInfo(term, Set.empty, Set.empty, false)

      // Integer predicates
      case BuiltinApp(function : BinaryBitVectorRelation, arguments) => {
        val left = arguments(0)
        val right = arguments(1)
        val resLeft = fixOverflow(left, sig, polarity, univVars, extVars)
        val resRight = fixOverflow(right, sig, polarity, univVars, extVars)
        val op: (Term, Term) => Term = (a: Term, b: Term) => BuiltinApp(function, Seq(a, b))
        val resCombined = resLeft.combine(op)(resRight)
        
        applyChecks(resCombined, polarity)
      }

      // TODO change to have predicates 
      case BuiltinApp(function, arguments) => {
          // clean up arguments and get their checks
          val (cleanArgs, univChecks, extChecks, containsUnivVar) = combineResults(arguments.map(fixOverflow(_, sig, polarity, univVars, extVars)))
          val newTerm = BuiltinApp(function, cleanArgs)
          // include this term if it can overflow
          val allOverflowTerms = if (canOverflow(term)) {
            val newChecks = overflowCheck(newTerm, sig)
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
        val newSig = sig.withConstants(vars)
        val newUnivVars = univVars.++(vars.map(_ match {case AnnotatedVar(v, _) => v}))
        val bodyInfo = fixOverflow(body, newSig, polarity, newUnivVars, extVars)
        return bodyInfo.mapTerm(Forall(vars, _))
      }

      case Exists(vars, body) => {
        // put vars into new sig
        val newSig = sig.withConstants(vars)
        val newUnivVars = univVars.++(vars.map(_ match {case AnnotatedVar(v, _) => v}))
        val bodyInfo = fixOverflow(body, newSig, polarity, newUnivVars, extVars)
        return bodyInfo.mapTerm(Exists(vars, _))
      }

      // todo closure and no overflow semantics? Closure not allowed quantifiers, but it could have operators...
      // just check if overflow in arguments?
      case Closure(functionName, arg1, arg2, fixedArgs) => {
        val res1 = fixOverflow(arg1, sig, polarity, univVars, extVars)
        val res2 = fixOverflow(arg2, sig, polarity, univVars, extVars)
        val (cleanFixed, fixedUnivChecks, fixedExtChecks, fixedUnivVar) = combineResults(fixedArgs.map(fixOverflow(_, sig, polarity, univVars, extVars)))
        val univChecks = res1.univChecks | res2.univChecks | fixedUnivChecks
        val extChecks = res1.extChecks | res2.extChecks | fixedExtChecks
        val containsUnivVar = res1.containsUnivVar || res2.containsUnivVar || fixedUnivVar
        ResultInfo(Closure(functionName, res1.cleanTerm, res2.cleanTerm, cleanFixed), univChecks, extChecks, containsUnivVar)
      }
      case ReflexiveClosure(functionName, arg1, arg2, fixedArgs) => {
        val res1 = fixOverflow(arg1, sig, polarity, univVars, extVars)
        val res2 = fixOverflow(arg2, sig, polarity, univVars, extVars)
        val (cleanFixed, fixedUnivChecks, fixedExtChecks, fixedUnivVar) = combineResults(fixedArgs.map(fixOverflow(_, sig, polarity, univVars, extVars)))
        val univChecks = res1.univChecks | res2.univChecks | fixedUnivChecks
        val extChecks = res1.extChecks | res2.extChecks | fixedExtChecks
        val containsUnivVar = res1.containsUnivVar || res2.containsUnivVar || fixedUnivVar
        ResultInfo(ReflexiveClosure(functionName, res1.cleanTerm, res2.cleanTerm, cleanFixed), univChecks, extChecks, containsUnivVar)
      }

      
      case Eq(left, right) => {
        val resLeft = fixOverflow(left, sig, polarity, univVars, extVars)
        val resRight = fixOverflow(right, sig, polarity, univVars, extVars)
        val resCombined = resLeft.combine((a,b) => Eq(a, b))(resRight)

        // If uncaught overflows, check
        if (!resCombined.univChecks.isEmpty || !resCombined.extChecks.isEmpty){
          applyChecks(resCombined, polarity)
        } else {
          resCombined
        }
      }

      // TODO if then else

      case Iff(left, right) => {
        // NOTE unsure about polarity here? They have to match...
        // It might need to be two implications?
        val resLeft = fixOverflow(left, sig, polarity, univVars, extVars)
        val resRight = fixOverflow(right, sig, polarity, univVars, extVars)
        val resCombined =  resLeft.combine(Iff(_, _))(resRight)
      
        // If uncaught overflows, check
        if (!resCombined.univChecks.isEmpty || !resCombined.extChecks.isEmpty){
          applyChecks(resCombined, polarity)
        } else {
          resCombined
        }
      }

      case Implication(left, right) => {
        val resLeft = fixOverflow(left, sig, !polarity, univVars, extVars)
        val resRight = fixOverflow(right, sig, polarity, univVars, extVars)
        return resLeft.combine(Implication(_, _))(resRight)
      }

      case Not(body) => {
        val result = fixOverflow(body, sig, !polarity, univVars, extVars)
        result.mapTerm(Not(_))
      }

      case AndList(arguments) => {
        val (cleanArgs, univChecks, extChecks, containsUnivVar) = combineResults(arguments.map(fixOverflow(_, sig, polarity, univVars, extVars)))
        ResultInfo(AndList(cleanArgs), univChecks, extChecks, containsUnivVar)
      }
      case OrList(arguments) => {
        val (cleanArgs, univChecks, extChecks, containsUnivVar) = combineResults(arguments.map(fixOverflow(_, sig, polarity, univVars, extVars)))
        ResultInfo(OrList(cleanArgs), univChecks, extChecks, containsUnivVar)
      }

      
      case App(functionName, arguments) => {
        val (cleanArgs, univChecks, extChecks, containsUnivVar) = combineResults(arguments.map(fixOverflow(_, sig, polarity, univVars, extVars)))
        val combined = ResultInfo(App(functionName, cleanArgs), univChecks, extChecks, containsUnivVar)
        // Non-predicate, no check needed. Predicate, add checks
        if (isPredicate(functionName, sig)){
          applyChecks(combined, polarity)
        } else {
          combined
        }
      }

      // Distinct is a predicate, so we need checks!
      case Distinct(arguments) => {
        val (cleanArgs, univChecks, extChecks, containsUnivVar) = combineResults(arguments.map(fixOverflow(_, sig, polarity, univVars, extVars)))
        val combined = ResultInfo(Distinct(cleanArgs), univChecks, extChecks, containsUnivVar)
        applyChecks(combined, polarity)
      }

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
      
    }
    
    def isPredicate(functionName: String, sig: Signature): Boolean = {
      sig.functionWithName(functionName) match {
        case None => Errors.Internal.impossibleState("Trying to check if function '" + functionName + "' is a predicate, but it is not in the signature.")
        case Some(fdecl) => fdecl.resultSort == BoolSort
      }
    }

    /**
      * Applies the checks in `currentInfo` to "hide" overflows. 
      * Keeps checks so they can be applied again if another comparison is used
      * @param currentInfo 
      * @param polarity
      * @return
      */
    def applyChecks(currentInfo: ResultInfo, polarity: Boolean): ResultInfo = {
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
      * 
      *
      * @param term
      * @param signature
      * @return A `Term` that will evaluate to true when `term` would cause an overflow.
      */
    def overflowCheck(term: Term, signature: Signature): Term = term match {
      case BuiltinApp(function, arguments) => function match {
        case BvNeg => {
          // Overflow occurs when the value negated is the minimum value
          val body: Term = arguments(0)
          val bitwidth = bitvectorWidth(body, signature).get
          val minBV = BitVectorLiteral(minimumIntValue(bitwidth), bitwidth)
          return Eq(body, minBV)
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
          return Or(
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
          )
        }
        // Negate and check for addition, check both for overflow
        case BvSub => {
          Or(overflowCheck(bvSubtoPlus(term), signature), overflowCheck(BuiltinApp(BvNeg, arguments(1)), signature))
        }
        // Division will over/underflow with divide by zero
        case BvSignedDiv => checkDivideByZero(arguments, signature)
        case BvSignedMod => checkDivideByZero(arguments, signature)
        case BvSignedRem => checkDivideByZero(arguments, signature)
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

          Or(underflow, overflow)
        }
        case _ => Errors.Internal.impossibleState("Cannot find overflow check for term " + term.toString())
      }
      case _ => Errors.Internal.impossibleState("Cannot find overflow check for term " + term.toString())
    }
}

object NoOverflowBVTransformer extends NoOverflowBVTransformer {}