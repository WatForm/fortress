package fortress.solverinterface
import fortress.inputs.{SmtModelParser, SmtModelVisitor}
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

//        println("model from z3: \n" + model + "\n")

        val visitor: SmtModelVisitor = SmtModelParser.parse(model, theory.get.signature)

        val rawFunctionDefinitions: mutable.Set[FunctionDefinition] = visitor.getFunctionDefinitions.asScala

        val fortressName2SmtValue: mutable.Map[String, String] = visitor.getFortressName2SmtValue.asScala

        val smtValue2DomainElement: mutable.Map[String, DomainElement] = visitor.getSmtValue2DomainElement.asScala

        println("rawFunctionDefinitions: \n" + rawFunctionDefinitions + "\n")

        println("fortressName2SmtValue: \n" + fortressName2SmtValue + "\n")

        println("smtValue2DomainElement: \n" + smtValue2DomainElement + "\n")

        object Solution extends ParserBasedInterpretation(theory.get.signature) {
            override protected def getConstant(c: AnnotatedVar): Value = {
                smtValueToFortressValue(
                    fortressName2SmtValue(c.name),
                    c.sort,
                    smtValue2DomainElement
                )
            }

            override protected def getSort(s: Sort): Seq[Value] = {
                smtValue2DomainElement.values.filter(
                    domainElement => domainElement.sort == s
                ).toIndexedSeq
            }

            override protected def getFunctionDefinitions: Set[FunctionDefinition] = {
                rawFunctionDefinitions.filter( item => {
                    var flag: Boolean = false
                    for( f <- theory.get.signature.functionDeclarations ) {
                        if( f.name == item.name ) flag = true
                    }
                    flag
                })
            }.toSet

            override protected def getFunctionValues(f: FuncDecl, scopes: Map[Sort, Int]): Map[Seq[Value], Value] = {
                if( theory.get.signature.sorts.size == scopes.size ) {
                    Map.empty
                    // TODO: use ruomei's method
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
                    c <- theory.get.signature.constants
                    if DomainElement.interpretName(c.name).isEmpty
                } yield (c -> getConstant(c))
            }.toMap

            override def functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = {
                for( f <- theory.get.signature.functionDeclarations ) yield (f -> getFunctionValues(f, scopes))
            }.toMap

            override def functionDefinitions: Set[FunctionDefinition] = getFunctionDefinitions
        }
        Solution
    }

    protected def smtValueToFortressValue(
         value: String,
         sort: Sort,
         smtValueToDomainElement: mutable.Map[String, DomainElement]
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
