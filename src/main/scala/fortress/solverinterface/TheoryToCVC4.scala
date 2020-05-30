package fortress.solverinterface

import edu.stanford.CVC4.{
    ExprManager => CVC4ExprManager,
    Expr => CVC4Expr,
    SmtEngine => CVC4SmtEngine,
    Result => CVC4Result,
    Kind => CVC4Kind
}

import fortress.msfol._
import fortress.util.Errors

import scala.jdk.CollectionConverters._

class TheoryToCVC4(theory: Theory){
    System.loadLibrary("cvc4jni")
    val em = new CVC4ExprManager
    val smt = new CVC4SmtEngine(em)

    def convert: CVC4SmtEngine = {
        smt
    }
}
