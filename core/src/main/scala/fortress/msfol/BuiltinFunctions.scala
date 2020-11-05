package fortress.msfol

/** Represents various builtin for integers and bitvectors. */
sealed trait BuiltinFunction {
    
    // Given a sequence of input sorts, returns either the sort of what this
    // builtin function will output, or None if the inputs sorts are not valid
    // for this function.
    def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort]
}

/////////////
// Integers
/////////////
sealed trait UnaryIntegerFunction extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort) => Some(IntSort)
        case _ => None
    }
}

sealed trait BinaryIntegerFunction extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(IntSort)
        case _ => None
    }
}

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
sealed trait UnaryBitVectorFunction extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n)) => Some(BitVectorSort(n))
        case _ => None
    }
}

sealed trait BinaryBitVectorFunction extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BitVectorSort(n))
        case _ => None
    }
}

sealed trait BinaryBitVectorRelation extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BoolSort)
        case _ => None
    }
}

case object BvPlus extends BinaryBitVectorFunction
case object BvSub extends BinaryBitVectorFunction
case object BvMult extends BinaryBitVectorFunction
case object BvSignedDiv extends BinaryBitVectorFunction
case object BvSignedRem extends BinaryBitVectorFunction
case object BvSignedMod extends BinaryBitVectorFunction

case object BvNeg extends UnaryBitVectorFunction


case object BvSignedLE extends BinaryBitVectorRelation
case object BvSignedLT extends BinaryBitVectorRelation
case object BvSignedGE extends BinaryBitVectorRelation
case object BvSignedGT extends BinaryBitVectorRelation
