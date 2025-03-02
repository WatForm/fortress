package fortress.msfol

/** Represents various builtin for integers and bitvectors. */
sealed trait BuiltinFunction {
    
    /** Given a sequence of input sorts, returns either the sort of what this
      * builtin function will output, or None if the inputs sorts are not valid
      * for this function.
      */
    def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort]
}

/////////////
// Integers 
/////////////

/** A function Int -> Int. */
sealed trait UnaryIntegerFunction extends BuiltinFunction {

    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort) => Some(IntSort)
        case _ => None
    }
}


/** A function Int x Int -> Int. */
sealed trait BinaryIntegerFunction extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(IntSort)
        case _ => None
    }
}

/** A relation Int x Int -> Bool. */
sealed trait BinaryIntegerRelation extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(BoolSort)
        case _ => None
    }
}

case object IntPlus extends BinaryIntegerFunction
case object IntSub extends BinaryIntegerFunction
case object IntMult extends BinaryIntegerFunction
case object IntDiv extends BinaryIntegerFunction
case object IntMod extends BinaryIntegerFunction

// Unary minus
case object IntNeg extends UnaryIntegerFunction

case object IntLE extends BinaryIntegerRelation
case object IntLT extends BinaryIntegerRelation
case object IntGE extends BinaryIntegerRelation
case object IntGT extends BinaryIntegerRelation

///////////////
// Bit Vectors
///////////////

/** A function BV(n) -> BV(n). */
sealed trait UnaryBitVectorFunction extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n)) => Some(BitVectorSort(n))
        case _ => None
    }
}

/** A function BV(n) x BV(n) -> BV(n). */
sealed trait BinaryBitVectorFunction extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BitVectorSort(n))
        case _ => None
    }
}

/** A function BV(n) x BV(n) -> Bool. */
sealed trait BinaryBitVectorRelation extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BoolSort)
        case _ => None
    }
}

/** A function BV(n) x BV(m) -> BV(n + m) */
sealed trait BitVectorConcatFunction extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) => Some(BitVectorSort(n + m))
        case _ => None
    }
}

case object BvPlus extends BinaryBitVectorFunction
case object BvSub extends BinaryBitVectorFunction
case object BvMult extends BinaryBitVectorFunction
case object BvSignedDiv extends BinaryBitVectorFunction
case object BvSignedRem extends BinaryBitVectorFunction
case object BvSignedMod extends BinaryBitVectorFunction

// Unary minus
case object BvNeg extends UnaryBitVectorFunction

case object BvSignedLE extends BinaryBitVectorRelation
case object BvSignedLT extends BinaryBitVectorRelation
case object BvSignedGE extends BinaryBitVectorRelation
case object BvSignedGT extends BinaryBitVectorRelation


case object BvConcat extends BitVectorConcatFunction


sealed trait NAryBooleanPredicate extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] =
        if (sorts.forall(_ == BoolSort)) Some(BoolSort)
        else None
}

// Custom SMTLIB predicates passed directly through to the SMT solver for testing
case class CustomPred(smtlib: String) extends NAryBooleanPredicate


/*
 * Casting between Int and Bitvector
 */

case class CastIntToBV(bitwidth: Int) extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort) => Some(BitVectorSort(bitwidth))
        case _ => None
    }
}

case object CastBVToInt extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(_)) => Some(IntSort)
        case _ => None
    }
}