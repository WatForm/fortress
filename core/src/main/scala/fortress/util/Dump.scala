package fortress.util

import fortress.msfol._
import java.io.StringWriter
import fortress.operations.SmtlibConverter

object Dump {
    def theoryToSmtlib(theory: Theory): String = {
        val writer = new StringWriter()
        val converter = new SmtlibConverter(writer)
        converter.writeTheory(theory)
        return writer.toString()
    }

    def termToSmtlib(term: Term): String = {
        val writer = new StringWriter()
        val converter = new SmtlibConverter(writer)
        converter.write(term)
        return writer.toString()
    }

}