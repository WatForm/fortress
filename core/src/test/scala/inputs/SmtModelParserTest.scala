import fortress.inputs._
import fortress.modelfind._
import fortress.msfol._
import fortress.problemstate.{ExactScope, NonExactScope}
import org.scalatest._

import scala.jdk.CollectionConverters._
import scala.jdk.OptionConverters._
import scala.util.Using

class SmtModelParserTest extends UnitSuite {
    test("parse with domain element"){
        val testString = "(declare-sort |univ| 0)(declare-fun |inthis/Univ_0| (|univ|) Bool)(declare-const |_@1univ| |univ|)(declare-const |_@2univ| |univ|)(declare-const |_@3univ| |univ|)(assert (distinct |_@1univ| |_@2univ| |_@3univ|))(assert (<= (+ (+ (ite (|inthis/Univ_0| |_@1univ|) 1 0) (ite (|inthis/Univ_0| |_@2univ|) 1 0)) (ite (|inthis/Univ_0| |_@3univ|) 1 0)) 3))(assert (< (- 1) 0))"
        val univ = SortConst("univ")
        val inThis = FuncDecl("inThis/Univ_0", univ, BoolSort)
        val sig = Signature.empty
            .withSort(univ)
        val visit = SmtModelParser.parse(testString, sig)
        println(visit.getTheory())
    }
}