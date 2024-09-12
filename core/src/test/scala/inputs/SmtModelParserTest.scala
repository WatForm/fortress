import fortress.inputs._
import fortress.modelfinders._
import fortress.msfol._
import fortress.problemstate.{ExactScope, NonExactScope}
import org.scalatest._

import scala.jdk.CollectionConverters._
import scala.jdk.OptionConverters._
import scala.util.Using

/*
for readability, this is the first test:
(declare-sort |univ| 0)
(declare-fun |inthis/Univ_0| (|univ|) Bool)
(declare-const |_@1univ| |univ|)
(declare-const |_@2univ| |univ|)
(declare-const |_@3univ| |univ|)

(assert (distinct |_@1univ| |_@2univ| |_@3univ|))
(assert (<= (+ (+ (ite (|inthis/Univ_0| |_@1univ|) 1 0) (ite (|inthis/Univ_0| |_@2univ|) 1 0)) (ite (|inthis/Univ_0| |_@3univ|) 1 0)) 3))

(assert (< (- 1) 0))
*/

class SmtModelParserTest extends UnitSuite {
    test("parse with domain element"){
        val testString = "(declare-sort |univ| 0)(declare-fun |inthis/Univ_0| (|univ|) Bool)(declare-const |_@1univ| |univ|)(declare-const |_@2univ| |univ|)(declare-const |_@3univ| |univ|)(assert (distinct |_@1univ| |_@2univ| |_@3univ|))(assert (<= (+ (+ (ite (|inthis/Univ_0| |_@1univ|) 1 0) (ite (|inthis/Univ_0| |_@2univ|) 1 0)) (ite (|inthis/Univ_0| |_@3univ|) 1 0)) 3))(assert (< (- 1) 0))"
        val univ = SortConst("univ")
        val inThis = FuncDecl("inThis/Univ_0", univ, BoolSort)
        val sig = Signature.empty
            .withSort(univ)
        val visit = SmtModelParser.parse(testString, sig)
        val theory = visit.getTheory()
        theory.axioms should contain (Distinct(DomainElement(1, univ), DomainElement(2, univ), DomainElement(3, univ)))
        theory.axioms should contain (BuiltinApp(IntLT, Seq(BuiltinApp(IntNeg, Seq(IntegerLiteral(1))), IntegerLiteral(0))))
    }

/*
for readability, this is the second test:
(declare-sort univ 0)
(declare-fun inthis/Univ_0 (univ) Bool)
(declare-const _@1univ univ)
(declare-const _@2univ univ)
(declare-const _@3univ univ)
(assert (= (as _@2univ inthis/Univ_0) (as _@2univ inthis/Univ_0))) 

Note that the (as x y) parts of CVC5 are turned directly into variables
that are evaluated to get their match to a domain element.
*/

    test("parse with domain element cvc5"){
        val testString = "(declare-sort univ 0)(declare-fun inthis/Univ_0 (univ) Bool)(declare-const _@1univ univ)(declare-const _@2univ univ)(declare-const _@3univ univ) (assert (= (as _@2univ inthis/Univ_0) (as _@2univ inthis/Univ_0))) "
        val univ = SortConst("univ")
        val inThis = FuncDecl("inThis/Univ_0", univ, BoolSort)
        val sig = Signature.empty
            .withSort(univ)
        val visit = SmtModelParser.parse(testString, sig)
        val theory = visit.getTheory()
        //System.out.println(theory.axioms);
        theory.axioms should contain (Eq(Var("(as_@2univinthis/Univ_0)"),Var("(as_@2univinthis/Univ_0)") ))
    }

    test("parse with domain element cvc5 with quotes") {
        val testString = "(declare-sort |univ| 0)(declare-fun |inthis/Univ_0| (|univ|) Bool)(declare-const |_@1univ| |univ|)(declare-const |_@2univ| |univ|)(declare-const |_@3univ| |univ|) (assert (= (as |_@2univ| |inthis/Univ_0|) (as |_@2univ| |inthis/Univ_0|))) ";
        val univ = SortConst("univ")
        val sig = Signature.empty
            .withSort(univ)
        val visit = SmtModelParser.parse(testString, sig)
        val theory = visit.getTheory
        theory.axioms should contain (Eq(Var("(as_@2univinthis/Univ_0)"), Var("(as_@2univinthis/Univ_0)") ))
    }
}