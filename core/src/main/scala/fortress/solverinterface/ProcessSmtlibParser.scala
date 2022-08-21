package fortress.solverinterface
import fortress.inputs.SmtModelVisitor
import fortress.interpretation.Interpretation
import fortress.util.{Errors, NameConverter}
import fortress.interpretation._
import fortress.msfol.{AnnotatedVar, BitVectorLiteral, BitVectorSort, BoolSort, Bottom, DomainElement, FuncDecl, FunctionDefinition, IntSort, IntegerLiteral, Sort, SortConst, Top, Value}

import scala.jdk.CollectionConverters._
import scala.annotation.varargs
import scala.collection.mutable // So we can call Scala varargs methods from Java

trait ProcessSmtlibParser extends ProcessBuilderSolver {

    override def solution: Interpretation = {
        Errors.Internal.assertion(processSession.nonEmpty, "Cannot get instance without a live process")

        val model: String = getModel

        val visitor: SmtModelVisitor = SmtModelParser.parse(model)

        val functionDefinitions: mutable.Set[FunctionDefinition] = visitor.getFunctionDefinitions.asScala

        val fortressName2SmtValue: mutable.Map[String, String] = visitor.getFortressName2SmtValue.asScala

        val smtValue2DomainElement: mutable.Map[String, DomainElement] = visitor.getSmtValue2DomainElement.asScala

        object Solution extends ParserBasedInterpretation(signature = theory.get.signature, scopeMap = scopes.get) {
            override protected def evaluateConstant(c: AnnotatedVar): Value = {
                smtValueToFortressValue(fortressName2SmtValue(c.name), )
            }

            override protected def evaluateSort(s: Sort): Seq[Value] = ???

            override protected def evaluateFunction(f: FuncDecl, scopes: Map[Sort, Int]): Map[Seq[Value], Value] = ???

            override protected def evaluateFunctionDefinition(): Set[FunctionDefinition] = ???
        }


        null
    }

    protected def smtValueToFortressValue(
         value: String,
         sort: Sort,
         smtValueToDomainElement: Map[String, DomainElement]
     ): Value = {
        sort match {
            case SortConst(_) => {
                if (smtValueToDomainElement.keySet.contains(value))
                    smtValueToDomainElement(value)
                else
                    DomainElement.interpretName(NameConverter.nameWithoutAffix(value)).get
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
            case BitVectorSort(bitwidth) => value match {
                case ProcessBuilderSolver.bitVecLiteral(radix, digits) => radix match {
                    case "x" => BitVectorLiteral(Integer.parseInt(digits, 16), bitwidth)
                    case "b" => BitVectorLiteral(Integer.parseInt(digits, 2),  bitwidth)
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

}
