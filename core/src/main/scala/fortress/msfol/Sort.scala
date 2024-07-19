package fortress.msfol

import fortress.util.Errors
import fortress.util.NameConverter

/** Represents a sort. */
sealed abstract class Sort {
    def name: String
    def isBuiltin: Boolean
    override def toString: String = name
}

/** An uninterpreted sort. */
case class SortConst private (name: String) extends Sort {
    Errors.Internal.precondition(name.length > 0, "Cannot create sort with empty name");
    Errors.Internal.precondition(! Names.isIllegal(name), "Illegal sort name " + name);
    //Errors.Internal.precondition(! name.contains(" "), "Cannot make sort constant with space " + name)
    Errors.Internal.precondition(! Sort.nameMimicsBuiltin(name), "Cannot make sort constant with name " + name)
    Errors.Internal.precondition(! name.contains("|"), "Cannot create const with '|' in name: " + name);

    override def isBuiltin: Boolean = false
}

/** The Bool sort. */
case object BoolSort extends Sort {
    def name: String = "Bool"
    override def isBuiltin: Boolean = true
}

/** The Int sort. */
case object IntSort extends Sort {
    def name: String = "Int"
    override def isBuiltin: Boolean = true
}

/*
2024-07-15 NAD
This was an attempt to distinguish uses of IntSorts that must be bound (because of quantification)
from those that can remain Unbounded

case object BoundedIntSort extends Sort {
    override def name: String = "BoundedIntSort"

    override def isBuiltin: Boolean = true
}

case object UnBoundedIntSort extends Sort {
    // use the same name with Int, because UnboundedIntSort & IntSort make no difference to user, only used for fortress transformer
    override def name: String = "Int"

    override def isBuiltin: Boolean = true
}
*/

/** The BitVector sort for a given bitwidth. */
case class BitVectorSort private (bitwidth: Int) extends Sort {
    def name: String = "BitVec" + bitwidth.toString
    override def isBuiltin: Boolean = true
}

object BitVectorSort {
    val namingPattern: scala.util.matching.Regex = "BitVec[0-9]*".r
}

object Sort {
    def mkSortConst(name: String): Sort = 
        SortConst(NameConverter.nameWithoutQuote(name))

    def mkIntSort(): Sort = IntSort
    
    val Bool: Sort = BoolSort
    val Int: Sort = IntSort
    /*
    val BoundedInt: Sort = BoundedIntSort
    val UnBoundedInt: Sort = UnBoundedIntSort
    */
    
    def BitVector(bitwidth: Int): Sort = BitVectorSort(bitwidth)
    
    def nameMimicsBuiltin(name: String): Boolean = {
        name == "Bool" || name == "Int" || name == "Real" || name.startsWith("BitVec")
    }
}
