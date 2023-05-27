package fortress.operations

import fortress.msfol._
import fortress.util._

import java.io._
/*
    Implement the monotonicity checking algorithm.
    The algorithm was first presented in the paper "Sort It Out with Monotonicity" by Koen Claessen, Ann Lilliestrom, and Nicholas Smallbone.
    Assume the input axioms are in conjunctive normal form.
    Use Z3 as the backend solver, so we do not need more configurations to build Fortress.
 */
class Monotonicity(theory: Theory) {
    var sort: Sort = null
    val sorts: Set[Sort] = theory.sorts
    var varMap: Map[Term, Map[Var, Sort]] = Map.empty
    val functions: Set[FuncDecl] = theory.functionDeclarations
    val predicates: Set[FuncDecl] = functions.filter(_.resultSort == BoolSort)
    var result: Map[Sort, Boolean] = Map.empty
    var variables: Map[Var, Sort] = Map.empty


    // to CNF
    var cnfAxioms: Set[Term] = {
        var tmp: Set[Term] = Set.empty
        for(axiom <- theory.axioms) {
            val (cnf, map) = NormalForms.getVariablesAndToCNF(axiom)
            tmp = tmp + cnf
            varMap = varMap + (cnf -> map)
        }
        tmp
    }

    var constants: Set[AnnotatedVar] = {
        var tmp: Set[AnnotatedVar] = Set.empty
        for (pred <- predicates) tmp = tmp + AnnotatedVar(Var(pred.name + "_T"), BoolSort) + AnnotatedVar(Var(pred.name + "_F"), BoolSort)
        tmp
    }


    def initAssertions(): Set[Term] = for (pred <- predicates) yield OrList(Not(Var(pred.name + "_T")), Not(Var(pred.name + "_F")))

    // store the constraints for checking monotonicity
    var assertions: Set[Term] = initAssertions()

    def check(): Map[Sort, Boolean] = {
        for(s <- sorts) {
            sort = s
            assertions = initAssertions()
            val isMonotonic: Boolean = {
                for(axiom <- cnfAxioms) {
                    variables = varMap(axiom)
                    monotone(axiom)
                }
                if(assertions.isEmpty) true
                else if(assertions.contains(Bottom)) false
                else solve()
            }
            result = result + (s -> isMonotonic)
        }
        result
    }

    // monotone((C1 ∧ .. ∧ Cn), sort)
    def monotone(formula: Term): Unit = formula match {
        case AndList(clauses) => clauses.foreach(monotoneClause)
        case OrList(literals) => monotoneClause(formula)
        case f => monotoneLiteral(Seq(f), f)
        //            Errors.Internal.impossibleState("An formula should be the conjunction of clauses.")
    }

    // monotone((l1 ∨ .. ∨ ln), sort)
    def monotoneClause(clause: Term): Unit = clause match {
        case OrList(literals) => literals.foreach(l => monotoneLiteral(literals, l))
        case Eq(_, _) | Not(Eq(_, _)) | App(_, _) | Not(App(_, _)) => monotoneLiteral(Seq(clause), clause)
        case _ => Errors.Internal.impossibleState("A clause should be the disjunction of literals.")
    }

    // monotone(C, l, sort)
    def monotoneLiteral(literals: Seq[Term], literal: Term): Unit = literal match {
        case Eq(t1, t2) => {
            safe(literals, t1)
            safe(literals, t2)
        }
        case Not(Eq(l, r)) => ()
        case App(functionName, arguments) => {
            val _pf: Term = Not(Var(functionName + "_F"))
            arguments.foreach(t => safe(literals, t, _pf))
        }
        case Not(App(functionName, arguments)) => {
            val _pt: Term = Not(Var(functionName + "_T"))
            arguments.foreach(t => safe(literals, t, _pt))
        }
        case _ => {
            //            println("literal: " + literal.toString)
            //            Errors.Internal.impossibleState("Impossible literal format")
        }
    }

    def safe(literals: Seq[Term], t: Term): Unit = {
        var slits: Seq[Term] = Seq.empty
        safe(literals, t, slits) // 2
    }

    def safe(literals: Seq[Term], t: Term, add: Term): Unit = {
        var slits: Seq[Term] = Seq(add)
        safe(literals, t, slits) // 2
    }

    def safe(literals: Seq[Term], t: Term, slits: Seq[Term]): Unit = t match { // 2
        case Var(x) => {
            if (variables.contains(Var(x)) && variables(Var(x)) == sort) {
                var list: Seq[Term] = slits
                for (l <- literals) list = guards(l, t) match {
                    case Some(term) => list :+ term
                    case None => list
                }
                assertions = assertions + (if (list.size > 1) OrList(list) else list.head)
            }
        }
        case _ => ()
    }

    // guards(l, X)
    def guards(literal: Term, x: Term): Option[Term] = literal match {
        case App(functionName, arguments) => if(arguments.contains(x)) Some(Var(functionName + "_T")) else None
        case Not(App(functionName, arguments)) => if (arguments.contains(x)) Some(Var(functionName + "_F")) else None
        case Not(Eq(l, r)) => if(l==x || r==x) Some(Top) else None
        case _ => Some(Bottom)
    }

    def solve(): Boolean = {
        val process: Process = new ProcessBuilder("z3", "-smt2", "-in").start()
        val in: BufferedWriter = new BufferedWriter(new OutputStreamWriter(process.getOutputStream))
        val out: BufferedReader = new BufferedReader(new InputStreamReader(process.getInputStream))
        // write to the process
        in.write("(set-logic ALL)\n")
        val converter = new SmtlibConverter(in)
        constants.foreach(converter.writeConst)
        assertions.foreach(converter.writeAssertion)
        in.write("(check-sat)\n")
        in.flush()
        // read from the process
        val result = out.readLine()
        in.close()
        out.close()
        process.destroy()
        if(result == "sat") true else false
    }
}
