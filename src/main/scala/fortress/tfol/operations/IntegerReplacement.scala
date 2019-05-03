// package fortress.tfol.operations
// 
// import fortress.tfol._
// import fortress.tfol.IntegerExtension._
// import fortress.tfol.BitVectorExtension._
// import scala.collection.immutable.Seq // Use immutable seq
// 
// object IntegerToBitVectorUnsigned {
//     def apply(term: Term, bitwidth: Int): Term = {
//         def recur(term: Term): Term = term match {
//             case Top() | Bottom() | Var(_) | DomainElement(_, _) | BitVectorLiteral(_, _) => term
//             case Not(p) => Not(recur(p))
//             case AndList(args) => AndList(args.map(recur))
//             case OrList(args) => OrList(args.map(recur))
//             case Distinct(args) => Distinct(args.map(recur))
//             case Implication(l, r) => Implication(recur(l), recur(r))
//             case Iff(l, r) => Iff(recur(l), recur(r))
//             case Eq(l, r) => Eq(recur(l), recur(r))
//             case App(f, args) => convertApp(f, args)
//             case Exists(vars, body) => {
//                 val newVars = vars.map(
//                     v => if (v.sort == IntType) { v.variable of BitVectorType(bitwidth) } else v
//                 )
//                 Exists(newVars, recur(body))
//             }
//             case Forall(vars, body) => {
//                 val newVars = vars.map(
//                     v => if (v.sort == IntType) { v.variable of BitVectorType(bitwidth) } else v
//                 )
//                 Forall(newVars, recur(body))
//             }
//             case TC(r, arg1, arg2) => TC(r, recur(arg1), recur(arg2))
//             case IntegerLiteral(n) => BitVectorLiteral(n, bitwidth)
//         }
//         def convertApp(f: String, args: Seq[Term]): Term = (f, args) match {
//             case (`plus`, args) => App(bvadd, args)
//             case (`minus`, Seq(oneArg)) => App(bvneg, oneArg)
//             case (`minus`, args) => App(bvsub, args)
//             case (`times`, args) => App(bvmul, args)
//             case (`div`, args) => ???
//             case (`mod`, args) => ???
//             case (`abs`, args) => ???
//             case (`LE`, args) => App(bvule, args)
//             case (`LT`, args) => App(bvult, args)
//             case (`GE`, args) => App(bvuge, args)
//             case (`GT`, args) => App(bvugt, args)
//             case _ => App(f, args)
//         }
//         recur(term)
//     }
// }
