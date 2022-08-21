package fortress.solverinterface

import java.io._

import fortress.data.CartesianSeqProduct
import fortress.msfol._
import fortress.interpretation._
import fortress.modelfind._
import fortress.util._
import fortress.solverinterface._
import fortress.operations.SmtlibConverter

import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

trait ProcessBuilderSolver extends SolverSession {
    protected var processSession: Option[ProcessSession] = None
    protected var theory: Option[Theory] = None
    protected var scopes: Option[Map[Sort, Scope]] = None
    
    @throws(classOf[java.io.IOException])
    override def close(): Unit = {
        processSession.foreach(_.close())
    }
    
    protected override def finalize(): Unit = close()

    def getModel: String = {
        var model: String = ""
        processSession.get.write("(get-model)\n")
        processSession.get.flush()
        var line: String = processSession.get.readLine()
        while ({line = processSession.get.readLine(); line != ")"}) {
            model ++= line + "\n"
        }
        model
    }
}

object ProcessBuilderSolver {
    val smt2Model: Regex = """^\(\((\S+|\(.+\)) (\S+|\(.+\))\)\)$""".r
    val bitVecType: Regex = """\(_ BitVec (\d+)\)""".r
    val bitVecLiteral: Regex = """^#(.)(.+)$""".r
    val bitVecExpr: Regex = """\(_ bv(\d+) (\d+)\)""".r
    val bitVecExprCondensed: Regex = """(\d+)aaBitVecExpraa(\d+)""".r
    val negativeInteger: Regex = """\(- (\d+)\)""".r
    val negativeIntegerCondensed: Regex = """aaNegativeIntaa(\d+)""".r
}