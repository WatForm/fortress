package fortress.operations

import fortress.msfol._
import fortress.data.NameGenerator
import fortress.problemstate._
import fortress.util.Errors
import fortress.util.IntegerSize._
import fortress.util.Extensions.IntExtension
import java.lang.IllegalArgumentException
import java.util.ArrayList

import scala.jdk.CollectionConverters._


/** Transforms expressions so that operations that cause overflows
  * cause the quantified instance they are in to be ignored.
  * Hoists the checks to be at the quantifier level
  */
class NoOverflowBVHoistTransformer(topLevelTerm: Term, signature: Signature, scopes: Map[Sort, Scope], nameGen: NameGenerator){
    // todo might want to make all added negations check for double negation.
    // todo does negation and check add even work for sub? Do we check negation overflow?

    // Review... I don't think this matches exactly right.  forall x. (x + IntMax + IntMax) & A?? what if A is false? It should always overflow but also should be false

    /** Finds all subterms that can make the current quantifier cause an overflow
     * Returns current, non-overflow term and a sequence of terms that will be True if an unchecked overflow occurs inside the current term
    */
    def fixOverflow(term: Term, sig: Signature): (Term, Set[Term]) = term match {
      case _: LeafTerm => (term, Set.empty)

      case BuiltinApp(function, arguments) => {
          // clean up arguments and get their checks
          val (cleanArgs, argOverflowableTerms) = arguments.map(fixOverflow(_, sig)).unzip
          val newTerm = BuiltinApp(function, cleanArgs)
          // include this term if it can overflow
          val allOverflowTerms = if (canOverflow(term)) 
            argOverflowableTerms.toSet.flatten.incl(newTerm)
            else argOverflowableTerms.toSet.flatten
          (newTerm, allOverflowTerms)
      }

      case Forall(vars, body) => {
        // put vars into new sig
        val newSig = sig.withConstantDeclarations(vars)
        val (cleanBody, overflowableTerms) = fixOverflow(body, newSig)
        (replaceForallBody(cleanBody, overflowableTerms), Set.empty)
      }

      case Exists(vars, body) => {
        val newSig = sig.withConstantDeclarations(vars)
        val (cleanBody, overflowableTerms) = fixOverflow(body, newSig)
        (replaceExistsBody(cleanBody, overflowableTerms), Set.empty)
      }

      // todo closure and no overflow semantics? Closure not allowed quantifiers, but it could have operators...
      // just check if overflow in arguments?
      case Closure(functionName, arg1, arg2, fixedArgs) => {
        val (clean1, overflow1) = fixOverflow(arg1, sig)
        val (clean2, overflow2) = fixOverflow(arg2, sig)
        val (cleanFixed, fixedOverflowsSeq) = fixedArgs.map(fixOverflow(_, sig)).unzip
        val fixedOverflows = fixedOverflowsSeq.toSet.flatten
        val allOverflowChecks = fixedOverflows | overflow1 | overflow2
        (Closure(functionName, clean1, clean2, cleanFixed), allOverflowChecks)
      }
      case ReflexiveClosure(functionName, arg1, arg2, fixedArgs) => {
        val (clean1, overflow1) = fixOverflow(arg1, sig)
        val (clean2, overflow2) = fixOverflow(arg2, sig)
        val (cleanFixed, fixedOverflowsSeq) = fixedArgs.map(fixOverflow(_, sig)).unzip
        val fixedOverflows = fixedOverflowsSeq.toSet.flatten
        val allOverflowChecks = fixedOverflows | overflow1 | overflow2
        (ReflexiveClosure(functionName, clean1, clean2, cleanFixed), allOverflowChecks)
      }
      case Eq(left, right) => {
        val (cleanLeft, overflowLeft) = fixOverflow(left, sig)
        val (cleanRight, overflowRight) = fixOverflow(right, sig)
        (Eq(cleanLeft, cleanRight), overflowLeft | overflowRight)
      }
      // TODO if then else
      case Iff(left, right) => {
        val (cleanLeft, overflowLeft) = fixOverflow(left, sig)
        val (cleanRight, overflowRight) = fixOverflow(right, sig)
        (Iff(cleanLeft, cleanRight), overflowLeft | overflowRight)
      }

      case Implication(left, right) => {
        val (cleanLeft, overflowLeft) = fixOverflow(left, sig)
        val (cleanRight, overflowRight) = fixOverflow(right, sig)
        (Implication(cleanLeft, cleanRight), overflowLeft | overflowRight)
      }

      case Not(body) => {
        val (cleanBody, overflows) = fixOverflow(body, sig)
        (Not(cleanBody), overflows)
      }

      case AndList(arguments) => {
        val (cleanArgs, overflowChecks) = arguments.map(fixOverflow(_, sig)).unzip
        (AndList(cleanArgs), overflowChecks.toSet.flatten)
      }
      case OrList(arguments) => {
        val (cleanArgs, overflowChecks) = arguments.map(fixOverflow(_, sig)).unzip
        (AndList(cleanArgs), overflowChecks.toSet.flatten)
      }
      
      case App(functionName, arguments) => {
        val (cleanArgs, argOverflowableTermsSeq) = arguments.map(fixOverflow(_, sig)).unzip
        val argOverflowableTerms = argOverflowableTermsSeq.toSet.flatten
        (App(functionName, cleanArgs), argOverflowableTerms)
      }

      case Distinct(arguments) => {
        val (cleanArgs, argOverflowableTermsSeq) = arguments.map(fixOverflow(_, sig)).unzip
        val argOverflowableTerms = argOverflowableTermsSeq.toSet.flatten
        (Distinct(cleanArgs), argOverflowableTerms)
      }

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
      
    }


    def fixOverflow(term: Term): (Term, Set[Term]) = fixOverflow(term, signature)
    
    
    def replaceForallBody(cleanBody: Term, overflowableSubterms: Set[Term]): Term = {
      val overflowChecks = overflowableSubterms.map(overflowCheck)
      // overflows or original body
      OrList(cleanBody +: overflowChecks.toSeq)
    }

    def replaceExistsBody(cleanBody: Term, overflowableSubterms: Set[Term]): Term = {
      val overflowChecks = overflowableSubterms.map(overflowCheck)
      val doesNotOverflow = Not(AndList(overflowChecks.toSeq))
      And(doesNotOverflow, cleanBody)
    }

    // We will need to apply to children before adding current term
    def overflowableTerms(term: Term): Set[Term] = term match {
      case _: LeafTerm => Set.empty
      // Bit vector functions
      case BuiltinApp(function, arguments) => function match {
        // Functions are typically operators. These can all overflow
        case _: BinaryBitVectorFunction => arguments.map(overflowableTerms).fold[Set[Term]](Set(term))(_ union _)
        // Relations currently is just comparison ops, so we can just look at children
        case _: BinaryBitVectorRelation => arguments.map(overflowableTerms).fold(Set.empty)(_ union _)
        case BvNeg => arguments.map(overflowableTerms).fold[Set[Term]](Set(term))(_ union _)
        case _ => Set.empty
      }
      case OrList(arguments) => arguments.map(overflowableTerms).fold(Set.empty)(_ union _)
      case AndList(arguments) => arguments.map(overflowableTerms).fold(Set.empty)(_ union _)
      case Distinct(arguments) => arguments.map(overflowableTerms).fold(Set.empty)(_ union _)
      case Exists(vars, body) => Set.empty // Notably we need to do work inside it for the next part
      case Forall(vars, body) => Set.empty
      // TODO how do we want to handle if then else?
      case IfThenElse(condition, ifTrue, ifFalse) => overflowableTerms(condition) | overflowableTerms(ifTrue) | overflowableTerms(ifFalse)

      case Eq(left, right) => overflowableTerms(left) union overflowableTerms(right)
      case Iff(left, right) => overflowableTerms(left) union overflowableTerms(right)
      case Implication(left, right) => overflowableTerms(left) union overflowableTerms(right)
      case Not(body) => overflowableTerms(body)
      case _ => Set.empty
    }

    def bvSubtoPlus(term :Term): Term = term match {
      case BuiltinApp(BvSub, Seq(x, y)) => BuiltinApp(BvPlus, x, BuiltinApp(BvNeg, y))
      case _ => Errors.Internal.impossibleState(term.toString() + " is not an app of BvSub!")
    }
    def bvSubtoPlus(args: Seq[Term]): Term = args match {
      case Seq(x, y) => BuiltinApp(BvPlus, x, BuiltinApp(BvNeg, y))
      case _ => Errors.Internal.impossibleState("Bad arguments for BvSub!")
    }
    /** Currently just turns a - b into a + (-b) as that they have the same result.
     * Further work could use constants and addition to trim bounds somehow. */
    def simplifyOverflowableTerms(overflowables: Set[Term]): Set[Term] = {
      overflowables.map(term => term match {
        case BuiltinApp(BvSub, args) => bvSubtoPlus(args)
        case _ => term
      })
    }

    /** Returns a term that will evaluate to true if the arguments to a division will over/underflow
     * due to a divide by zero. */
    def checkDivideByZero(arguments: Seq[Term]): Term = {
      Errors.Internal.precondition(arguments.length == 2)
      val denominator = arguments(1)
      val bitwidth = bitvectorWidth(denominator, signature).get
      val zero = BitVectorLiteral(0, bitwidth)
      return Eq(denominator, zero)
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
    /** Returns a term that will evaluate to True iff `term` will overflow or underflow.
     */
    def overflowCheck(term: Term): Term = term match {
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
        // Negate and check for addition
        case BvSub => overflowCheck(bvSubtoPlus(term))
        // Division will over/underflow with divide by zero
        case BvSignedDiv => checkDivideByZero(arguments)
        case BvSignedMod => checkDivideByZero(arguments)
        case BvSignedRem => checkDivideByZero(arguments)
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