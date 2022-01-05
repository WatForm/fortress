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
    
    @throws(classOf[java.io.IOException])
    override def close(): Unit = {
        processSession.foreach(_.close())
    }
    
    protected override def finalize(): Unit = close()
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