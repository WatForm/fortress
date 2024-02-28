package fortress.solverinterface

import fortress.inputs._
import fortress.interpretation._
import fortress.modelfind._
import fortress.msfol._
import fortress.operations._
import fortress.util._
import scala.util.matching.Regex
import scala.jdk.CollectionConverters._
import java.io.CharArrayWriter
import scala.collection.mutable

trait SMTLIBCLISession extends solver {
    // real smt-solver process ex: z3 or cvc4
    protected var processSession: Option[ProcessSession] = None

    protected var theory: Option[Theory] = None

    protected def processArgs: Seq[String]
    protected def timeoutArg(timeoutMillis: Milliseconds): String

    @throws(classOf[java.io.IOException])
    override def close(): Unit = {
        processSession.foreach(_.close())
    }

    override def setTheory(theory: Theory): Unit = {
        this.theory = Some(theory)
        processSession.foreach(_.close())
        processSession = Some(new ProcessSession(processArgs.asJava))
        // Convert & write theory
        val writer = processSession.get.inputWriter
        writer.write("(set-option :produce-models true)\n")
        writer.write("(set-logic ALL)\n")
        val converter = new SmtlibConverter(writer)
        converter.writeTheory(theory)
    }


    override def addAxiom(axiom: Term): Unit = {
        Errors.Internal.assertion(processSession.nonEmpty, "Cannot add axiom without a live process")
        val converter = new SmtlibConverter(processSession.get.inputWriter)
        converter.writeAssertion(axiom)
    }


    override def solve(timeoutMillis: Milliseconds): ModelFinderResult = {
        processSession.get.write(s"(set-option :timeout ${timeoutMillis.value})") // Doesn't work for CVC4
        processSession.get.write("(check-sat)\n")
        processSession.get.flush()

        val result = processSession.get.readLine()
        result match {
            case "sat" => ModelFinderResult.Sat
            case "unsat" => ModelFinderResult.Unsat
            case "unknown" => {
                processSession.get.write("(get-info :reason-unknown)\n")
                processSession.get.flush()

                val reason = processSession.get.readLine()

                if(reason.contains("timeout"))
                    ModelFinderResult.Timeout
                else
                    ModelFinderResult.Unknown
            }
            case _ => ErrorResult(s"Unrecognized result '${result}'" )
        }
    }

    // return a model if the theory is satisfiable, used by func viewModel
    override def solution: Interpretation = {
        Errors.Internal.assertion(processSession.nonEmpty, "Cannot get instance without a live process")

        val model: String = getModel

//        println("model from z3: \n" + model + "\n")

        val visitor: SmtModelVisitor = SmtModelParser.parse(model, theory.get.signature)

        val rawFunctionDefinitions: mutable.Set[FunctionDefinition] = visitor.getFunctionDefinitions.asScala

        val fortressName2SmtValue: mutable.Map[String, String] = visitor.getFortressName2SmtValue.asScala

        val smtValue2DomainElement: mutable.Map[String, DomainElement] = { // H!val!0 -> _@1H
            val pattern = ".+!val![0-9]*$"
            val raw: mutable.Map[String, DomainElement] = visitor.getSmtValue2DomainElement.asScala
            for( (s, d) <- raw ) {
                if( d == null && s.matches(pattern) ) {
//                    assert(s.matches(pattern), "Parse error, exit code: 1")
                    val temp = s.split("!val!") // "H!val!0" => "H" "0"
                    assert(temp.length == 2, "Parse error, exit code: 2")
                    val sort: Sort = Sort.mkSortConst(temp(0))
                    val de: DomainElement = Term.mkDomainElement(Integer.parseInt(temp(1)) + 1, sort);
                    raw.put(s, de)
                }
            }
            raw
        }


//        println("rawFunctionDefinitions: \n" + rawFunctionDefinitions + "\n")
//
//        println("fortressName2SmtValue: \n" + fortressName2SmtValue + "\n")
//
//        println("smtValue2DomainElement: \n" + smtValue2DomainElement + "\n")

        object Solution extends ParserBasedInterpretation(theory.get.signature) {
            override protected def getConstant(c: AnnotatedVar): Value = {
                smtValueToFortressValue(
                    fortressName2SmtValue(c.name), // H!val!0
                    c.sort, // H
                    smtValue2DomainElement
                )
            }

            override protected def getSort(s: Sort): Seq[Value] = {
                smtValue2DomainElement.values.filter(
                    domainElement => domainElement!=null && domainElement.sort == s
                ).toIndexedSeq
            }

            // replace smt-value in function definition with fortress domainElements
            // eg: H!val!0 -> _@1H
            def updateFunc(func: Term): Term = func match {
                case IfThenElse(a, b, c) => IfThenElse(updateFunc(a), updateFunc(b), updateFunc(c))
                case AndList(args) => AndList(args.map(updateFunc))
                case OrList(args) => OrList(args.map(updateFunc))
                case (distinct: Distinct) => updateFunc(distinct.asPairwiseNotEquals)
                case Implication(left, right) => Implication(updateFunc(left), updateFunc(right))
                case Iff(p, q) => Iff(updateFunc(p), updateFunc(q))
                case Forall(vars, body) => Forall(vars, updateFunc(body))
                case Exists(vars, body) => Exists(vars, updateFunc(body))
                case Not(body) => Not(updateFunc(body))
                case App(name, args) => App(name, args.map(updateFunc))
                case Closure(name, arg1, arg2, fixedArgs) => Closure(name, updateFunc(arg1), updateFunc(arg2), fixedArgs.map(updateFunc))
                case ReflexiveClosure(name, arg1, arg2, fixedArgs) => ReflexiveClosure(name, updateFunc(arg1), updateFunc(arg2), fixedArgs.map(updateFunc))
                case Eq(p, q) => Eq(updateFunc(p), updateFunc(q))
                case Var(name) => {
                    if(smtValue2DomainElement.contains(name)) smtValue2DomainElement(name)
                    else func
                }
                case _ => func
            }

            override protected def getFunctionDefinitions: Set[FunctionDefinition] = {
                val functionDefinitions = rawFunctionDefinitions.filter(item => {
                    var flag: Boolean = false
                    for (f <- theory.get.signature.functionDeclarations) {
                        if (f.name == item.name) flag = true
                    }
                    flag
                })
                functionDefinitions.map(fd => {
                    new FunctionDefinition(
                        fd.name,
                        fd.argSortedVar,
                        fd.resultSort,
                        updateFunc(fd.body)
                    )
                })
            }.toSet

            override protected def getFunctionValues(f: FuncDecl, scopes: Map[Sort, Int]): Map[Seq[Value], Value] = {
                if( theory.get.signature.sorts.size == scopes.size ) {
                    Map.empty
                }
                else Map.empty
            }

            /** Maps a sort to a sequence of values. */
            override def sortInterpretations: Map[Sort, Seq[Value]] = {
                for(sort<-theory.get.signature.sorts) yield sort -> getSort(sort)
            }.toMap ++ (theory.get.signature.enumConstants transform ((_, v) => v.map(x => DomainElement.interpretName(x.name).get)))

            /** Maps a constant symbol to a value. */
            override def constantInterpretations: Map[AnnotatedVar, Value] = {
                for{
                    c <- theory.get.signature.constantDeclarations
                    if DomainElement.interpretName(c.name).isEmpty
                } yield (c -> getConstant(c))
            }.toMap

            override def functionDefinitions: Set[FunctionDefinition] = getFunctionDefinitions

            override def functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = {
                for( f <- theory.get.signature.functionDeclarations ) yield (f -> getFunctionValues(f, scopes))
            }.toMap

        }
        Solution
    }

    protected def smtValueToFortressValue(
         value: String, // H!val!0
         sort: Sort,   // H
         smtValueToDomainElement: mutable.Map[String, DomainElement]
    ): Value = {

        object ProcessBuilderSolver {
            val smt2Model: Regex = """^\(\((\S+|\(.+\)) (\S+|\(.+\))\)\)$""".r
            val bitVecType: Regex = """\(_ BitVec (\d+)\)""".r
            val bitVecLiteral: Regex = """^#(.)(.+)$""".r
            val bitVecExpr: Regex = """\(_ bv(\d+) (\d+)\)""".r
            val bitVecExprCondensed: Regex = """(\d+)aaBitVecExpraa(\d+)""".r
            val negativeInteger: Regex = """\(- ?(\d+)\)""".r
            val negativeIntegerCondensed: Regex = """aaNegativeIntaa(\d+)""".r

            val  BitVectorLiteral: Regex = """BitVectorLiteral.+""".r
        }


        sort match {
            case SortConst(_) => {
                if (smtValueToDomainElement.keySet.contains(value))
                    smtValueToDomainElement(value)
                else
                    DomainElement.interpretName(NameConverter.nameWithoutQuote(value)).get
            }
            case BoolSort => value match {
                case "true" => Top
                case "false" => Bottom
                case _ => Errors.Internal.impossibleState
            }
            case IntSort => value match {
                case ProcessBuilderSolver.negativeInteger(digits) => IntegerLiteral(-(digits.toInt))
                case ProcessBuilderSolver.negativeIntegerCondensed(digits) => IntegerLiteral(-(digits.toInt))
                case _ => IntegerLiteral(value.toInt)
            }
            case UnBoundedIntSort => value match {
                case ProcessBuilderSolver.negativeInteger(digits) => IntegerLiteral(-(digits.toInt))
                case ProcessBuilderSolver.negativeIntegerCondensed(digits) => IntegerLiteral(-(digits.toInt))
                case _ => IntegerLiteral(value.toInt)
            }
            case BitVectorSort(bitwidth) => value match {
                case ProcessBuilderSolver.bitVecLiteral(radix, digits) => radix match {
                    case "x" => BitVectorLiteral.ensureSignedValue(Integer.parseInt(digits, 16), bitwidth)
                    case "b" => {
                        BitVectorLiteral.ensureSignedValue(Integer.parseInt(digits, 2),  bitwidth)
                    }
                    case _ => Errors.Internal.impossibleState
                }
                case ProcessBuilderSolver.bitVecExpr(digits, bitw) => {
                    Errors.Internal.assertion(bitw.toInt == bitwidth)
                    BitVectorLiteral(digits.toInt, bitwidth)
                }
                case ProcessBuilderSolver.bitVecExprCondensed(digits, bitw) => {
                    Errors.Internal.assertion(bitw.toInt == bitwidth)
                    BitVectorLiteral(digits.toInt, bitwidth)
                }
                case _ => Errors.Internal.impossibleState
            }
        }
    }


    // get solution in smt-lib format form solver by cmd "get-model"
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
