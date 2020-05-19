package fortress.msfol

import fortress.util.Errors

/** Represents a sort. */
sealed abstract class Sort {
    def name: String
    def isBuiltin: Boolean
    override def toString: String = name
}

case class SortConst private (name: String) extends Sort {
    Errors.precondition(name.length > 0, "Cannot create sort with empty name");
    Errors.precondition(! Names.isIllegal(name), "Illegal sort name " + name);
    Errors.precondition(! name.contains(" "), "Cannot make sort constant with space " + name)
    Errors.precondition(! Sort.nameMimicsBuiltin(name), "Cannot make sort constant with name " + name)
    
    override def isBuiltin: Boolean = false
}

case object BoolSort extends Sort {
    def name: String = "Bool"
    override def isBuiltin: Boolean = true
}

case object IntSort extends Sort {
    def name: String = "Int"
    override def isBuiltin: Boolean = true
}

case class BitVectorSort(bitwidth: Int) extends Sort {
    def name: String = "BitVec" + bitwidth.toString
    override def isBuiltin: Boolean = true
}

object BitVectorSort {
    val namingPattern: scala.util.matching.Regex = "BitVec[0-9]*".r
}

object Sort {
    def mkSortConst(name: String): Sort = SortConst(name)
    
    val Bool: Sort = BoolSort
    val Int: Sort = IntSort
    def BitVector(bitwidth: Int): Sort = BitVectorSort(bitwidth)
    
    def nameMimicsBuiltin(name: String): Boolean = {
        name == "Bool" || name == "Int" || name == "Real" || name.startsWith("BitVec")
    }
}
