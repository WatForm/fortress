package fortress.msfol

/** Represents various builtin for integers and bitvectors. */
sealed abstract class BuiltinFunction {
    
    // Given a sequence of input sorts, returns either the sort of what this
    // builtin function will output, or None if the inputs sorts are not valid
    // for this function.
    def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort]
}

/////////////
// Integers
/////////////
case object IntPlus extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(IntSort)
        case _ => None
    }
}

// Unary minus
case object IntNeg extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort) => Some(IntSort)
        case _ => None
    }
}
case object IntSub extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(IntSort)
        case _ => None
    }
}
case object IntMult extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(IntSort)
        case _ => None
    }
}
case object IntDiv extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(IntSort)
        case _ => None
    }
}
case object IntMod extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(IntSort)
        case _ => None
    }
}
case object IntLE extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(BoolSort)
        case _ => None
    }
}
case object IntLT extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(BoolSort)
        case _ => None
    }
}
case object IntGE extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(BoolSort)
        case _ => None
    }
}
case object IntGT extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(IntSort, IntSort) => Some(BoolSort)
        case _ => None
    }
}

///////////////
// Bit Vectors
///////////////
case object BvPlus extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BitVectorSort(n))
        case _ => None
    }
}
case object BvNeg extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n)) => Some(BitVectorSort(n))
        case _ => None
    }
}
case object BvSub extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BitVectorSort(n))
        case _ => None
    }
}
case object BvMult extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BitVectorSort(n))
        case _ => None
    }
}
case object BvSignedDiv extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BitVectorSort(n))
        case _ => None
    }
}
case object BvSignedRem extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BitVectorSort(n))
        case _ => None
    }
}
case object BvSignedMod extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BitVectorSort(n))
        case _ => None
    }
}
case object BvSignedLE extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BoolSort)
        case _ => None
    }
}
case object BvSignedLT extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BoolSort)
        case _ => None
    }
}
case object BvSignedGE extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BoolSort)
        case _ => None
    }
}
case object BvSignedGT extends BuiltinFunction {
    override def resultSortFromArgSorts(sorts: Seq[Sort]): Option[Sort] = sorts match {
        case Seq(BitVectorSort(n), BitVectorSort(m)) if n == m => Some(BoolSort)
        case _ => None
    }
}
