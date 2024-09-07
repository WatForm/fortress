/*
    Default solving mode used by fortress.
    All SMT CLI solvers share these functions to process the text CLI inputs and outputs
    Write axioms to one solver process and call check-sat multiple times.
 */

package fortress.solvers

import fortress.inputs._
import fortress.interpretation._
import fortress.modelfinders.{ErrorResult, ModelFinderResult}
import fortress.util._
import fortress.msfol._
import fortress.operations._

import scala.util.matching.Regex
import java.io.CharArrayWriter
import scala.jdk.CollectionConverters._
import scala.collection.mutable


class SMTLIBCliSolver extends Solver {

    protected def processArgs: Seq[String] = ???
    protected def timeoutArg(timeoutMillis: Milliseconds): String = ???
    protected var theory: Option[Theory] = None
    
    protected var processSession: Option[ProcessSession] = None

    private val convertedBytes: CharArrayWriter = new CharArrayWriter

    @throws(classOf[java.io.IOException])
    override def close(): Unit = {
        processSession.foreach(_.close())
    }

    override def setTheory(theory: Theory): Unit = {
        this.theory = Some(theory)
        convertedBytes.reset()
        convertedBytes.write("(set-option :produce-models true)\n")
        convertedBytes.write("(set-logic ALL)\n")
        val converter = new SmtlibConverter(convertedBytes)
        converter.writeTheory(theory)
    }

    override def addAxiom(axiom: Term): Unit = {
        Errors.Internal.assertion(processSession.nonEmpty, "Cannot add axiom without a live process")
        val converter = new SmtlibConverter(convertedBytes)
        converter.writeAssertion(axiom)
    }

    override def solve(timeoutMillis: Milliseconds): ModelFinderResult = {
        processSession.foreach(_.close())
        processSession = Some(new ProcessSession( { processArgs :+ timeoutArg(timeoutMillis) }.asJava))
        convertedBytes.writeTo(processSession.get.inputWriter)
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

        val smtValue2DomainElement: mutable.Map[String, DomainElement] = visitor.getSmtValue2DomainElement.asScala

        // If a domain element isn't mentioned anywhere in the axioms, Z3 might fail to generate it.
        // Hack around this by patching any such cases back in.
        val currentDEs = smtValue2DomainElement.values.toSet
        for (constant <- theory.get.constantDeclarations) {
            DomainElement.interpretName(constant.name) match {
                case None => // do nothing
                case Some(de) =>
                    if (!(currentDEs contains de)) {
                        // fake an SMT name for it... H!val!N
                        val fakeSmtName = s"${de.sort.name}!val!${de.index}"
                        fortressName2SmtValue.put(constant.name, fakeSmtName)
                        smtValue2DomainElement.put(fakeSmtName, de)
                    }
            }
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
            /*
            case UnBoundedIntSort => value match {
                case ProcessBuilderSolver.negativeInteger(digits) => IntegerLiteral(-(digits.toInt))
                case ProcessBuilderSolver.negativeIntegerCondensed(digits) => IntegerLiteral(-(digits.toInt))
                case _ => IntegerLiteral(value.toInt)
            }
            */
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
