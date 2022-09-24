package fortress.util

import fortress.msfol._
import java.io.StringWriter
import fortress.operations.SmtlibConverter
import fortress.transformers.ProblemState
import java.io.PrintWriter

class Dump {
    
}

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

    def problemStateToSmtlib(problemState: ProblemState): String = {
        val writer = new StringWriter()
        val converter = new SmtlibConverter(writer)

        converter.writeTheory(problemState.theory)
        writer.write('\n')
        writer.write(";")
        writer.write(smtlibScopeInfo(problemState.scopes))
        
        return writer.toString()
    }

    def smtlibScopeInfo(scopes: Map[Sort, Scope]): String = {
        val writer = new StringWriter()

        val asTuples = scopes.toSeq
        val scopesByType = asTuples.groupMap[String, (Sort, Int)](info => info match {
            case (_, ExactScope(_)) => "exact"
            case (_, NonExactScope(_)) => "nonexact"
        })(info => info match {
            case (sort, ExactScope(scope)) => (sort, scope)
            case (sort, NonExactScope(scope)) => (sort, scope)
        })

        writer.write("(set-info :exact-scope \"")
        scopesByType.getOrElse("exact", Seq.empty).foreach(info => {
            writer.write('(')
            writer.write(info._1.name)
            writer.write(' ')
            writer.write(info._2.toString())
            writer.write(')')
        })
        writer.write("\")\n")

        writer.write("(set-info :nonexact-scope \"")
        scopesByType.getOrElse("nonexact", Seq.empty).foreach(info => {
            writer.write('(')
            writer.write(info._1.name)
            writer.write(' ')
            writer.write(info._2.toString())
            writer.write(')')
        })
        writer.write("\")\n")

        return writer.toString()
    }

    def toFile(text: String, filepath: String): Unit = {
        val pw = new PrintWriter(filepath)
        pw.write(text)
        pw.close()
    }

}