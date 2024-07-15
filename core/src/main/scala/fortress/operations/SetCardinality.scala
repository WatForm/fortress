// need some sort of equivalent to
// case IfThenElse(condition, ifTrue, ifFalse) =>
//             OrList(
//                 AndList(removeItesForBoolTerm(condition), removeItesForBoolTerm(ifTrue)),
//                 AndList(Not(removeItesForBoolTerm(condition)),removeItesForBoolTerm(ifFalse))
//             )

// first step - need to caputure in the language when cardinality occurs

// BOOKMARK, UNFINISHED
// case Cardinality(SomePredicateStatement){
//     total = 0; // not really, we want total to be the sequence of statements
//     For x in Universe:
//     total += IfThenElse(SomePredicateStatement(x), 1, 0)
//     return total; // except we don't want to return the count, we want to return the predicate logic REPRESENTING the count
// }