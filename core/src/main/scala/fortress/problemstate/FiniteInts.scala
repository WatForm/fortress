package fortress.problemstate

/**
  * Contains info regarding how integers
  * have been finitizes
  *
  * TODO: minInt and maxInt should be in sync with scope of ints in Scopes mapping
  */

import fortress.msfol.Sort

case class FiniteInts (
    finiteIntSort:Sort,
    minInt:Int,
    maxInt:Int,
    fromInt:String,
    toInt:String
) {}
