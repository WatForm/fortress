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

trait ProcessSmtlibEvaluation extends ProcessBuilderSolver {

    override def solution: Interpretation = {
        Errors.verify(processSession.nonEmpty, "Cannot get instance without a live process")

        val fortressNameToSmtValue: Map[String, String] = getFortressNameToSmtValueMap(theory.get)
        
        val smtValueToDomainElement: Map[String, DomainElement] = (
            for {
                (name, value) <- fortressNameToSmtValue
                domainElement <- DomainElement.interpretName(name)
            } yield (value -> domainElement)
        ).toMap
        
        object Solution extends EvaluationBasedInterpretation(theory.get.signature) {
            override protected def evaluateConstant(c: AnnotatedVar): Value = {
                smtValueToFortressValue(
                    fortressNameToSmtValue(c.name),
                    c.sort,
                    smtValueToDomainElement
                )
            }
            
            override protected def evaluateFunction(f: FuncDecl, argList: Seq[Value]): Value = {
                processSession.get.write("(get-value ((")
                processSession.get.write(f.name)
                for(arg <- argList){
                    processSession.get.write(" ")
                    processSession.get.write(arg.toString)
                }
                processSession.get.write(")))")
                processSession.get.write("\n")
                processSession.get.flush()
                
                val str = processSession.get.readLine()
                val value = str match {
                    case ProcessBuilderSolver.smt2Model(name, value) => value
                    case _ => Errors.unreachable()
                }
                smtValueToFortressValue(value, f.resultSort, smtValueToDomainElement)
            }
            
            override protected def evaluateSort(sort: Sort): Seq[Value] = {
                smtValueToDomainElement.values.filter(
                    domainElement => domainElement.sort == sort
                ).toIndexedSeq
            }
        }
        Solution
    }
    
    private def getFortressNameToSmtValueMap(theory: Theory): Map[String, String] = {
        for(constant <- theory.constants){
            processSession.get.write("(get-value (")
            processSession.get.write(constant.name)
            processSession.get.write("))")
        }
        processSession.get.write("\n")
        processSession.get.flush()
        
        (for(constant <- theory.constants) yield {
            val str = processSession.get.readLine()
            str match {
                case ProcessBuilderSolver.smt2Model(name, value) => {
                    Errors.verify(constant.name == name, s""""${constant.name}" should be equal to "$name"""")
                    (constant.name -> value)
                }
                case _ => Errors.unreachable()
            }
        }).toMap
    }
    
    private def smtValueToFortressValue(
        value: String,
        sort: Sort,
        smtValueToDomainElement: Map[String, DomainElement]
    ): Value = {
            
        sort match {
            case SortConst(_) => smtValueToDomainElement(value)
            case BoolSort => value match {
                case "true" => Top
                case "false" => Bottom
                case _ => Errors.unreachable()
            }
            case IntSort => IntegerLiteral(value.toInt)
            case BitVectorSort(bitwidth) => value match {
                case ProcessBuilderSolver.bitVecLiteral(radix, digits) => radix match {
                    case "x" => BitVectorLiteral(Integer.parseInt(digits, 16), bitwidth)
                    case "b" => BitVectorLiteral(Integer.parseInt(digits, 2),  bitwidth)
                    case _ => Errors.unreachable()
                }
                case ProcessBuilderSolver.bitVecExpr(digits, bitw) => {
                    Errors.verify(bitw.toInt == bitwidth)
                    BitVectorLiteral(digits.toInt, bitwidth)
                }
                case _ => Errors.unreachable()
            }
        }
    }
}
