package fortress.solverinterface

import java.io._
import fortress.data.CartesianSeqProduct
import fortress.msfol._
import fortress.interpretation._
import fortress.inputs._
import fortress.modelfind._
import fortress.util._
import fortress.solverinterface._
import fortress.operations.SmtlibConverter

import java.util
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

trait ProcessSmtlibEvaluation extends ProcessBuilderSolver {

    override def solution: Interpretation = {
        Errors.Internal.assertion(processSession.nonEmpty, "Cannot get instance without a live process")

        val fortressNameToSmtValue: Map[String, String] = getFortressNameToSmtValueMap(theory.get)

        println("--------------------------fortress name to smt value -----------------------------\n")
        println(fortressNameToSmtValue.toString())
        println("\n--------------------------------------------------------------------------------\n")
        
        val smtValueToDomainElement: Map[String, DomainElement] = (
            for {
                (name, value) <- fortressNameToSmtValue
                domainElement <- DomainElement.interpretName(name)
            } yield (value -> domainElement)
        ).toMap

        println("--------------------------smt value to domain element -----------------------------\n")
        println(smtValueToDomainElement.toString())
        println("\n---------------------------------------------------------------------------------\n")

        // Get model and store it in a map from identifier to string tokens
        val smtInterpTokens: Map[String, Array[String]] = {
            processSession.get.write("(get-model)\n")
            processSession.get.flush()

            var line: String = null
            val smtInterpTokens = scala.collection.mutable.Map[String, Array[String]]()
            var currentFunc: String = null
            println("Model from z3: \n")
            while ({line = processSession.get.readLine(); line != ")"}) {

                println(line)

                // Replace expressions that has space in them, such as bit vector type, bit vector
                // expression and negative integer with their condensed form (remove spaces)
                line = line.replaceAll(ProcessBuilderSolver.bitVecType.regex, """BitVec$1""")
                line = line.replaceAll(ProcessBuilderSolver.bitVecExpr.regex, """$1aaBitVecExpraa$2""")
                line = line.replaceAll(ProcessBuilderSolver.negativeInteger.regex, """aaNegativeIntaa$1""")
                // Remove brackets and "and", split into tokens
                line = line.replaceAll("[()]", "")
                val tokens = line.split(" +").filterNot(_ == "").filterNot(_ == "and")
                // Store them in a map that maps each function name to a list of tokens
                if (tokens.length > 1 && tokens(0).equals("define-fun")) {
                    currentFunc = NameConverter.nameWithoutAffix(tokens(1))
                    smtInterpTokens(currentFunc) = Array[String]()
                }
                if (currentFunc != null) {
                    smtInterpTokens(currentFunc) ++= tokens
                }
            }
            println(")\n")
            smtInterpTokens.toMap
        }

        println("--------------------------smt Intrepretation tokens -----------------------------\n")
        println(smtInterpTokens.toString())
        println("\n---------------------------------------------------------------------------------\n")

        object Solution extends EvaluationBasedInterpretation(theory.get.signature) {

            // get constants
            override protected def evaluateConstant(c: AnnotatedVar): Value = {
                smtValueToFortressValue(
                    fortressNameToSmtValue(c.name),
                    c.sort,
                    smtValueToDomainElement
                )
            }

            protected def evaluateFunctionByGetValue(f: FuncDecl, argList: Seq[Value]): Value = {
                processSession.get.write("(get-value ((")
                processSession.get.write(NameConverter.nameWithAffix(f.name))
                for(arg <- argList){
                    processSession.get.write(" ")
                    if (arg.toString.equals("true") || arg.toString.equals("false"))
                        processSession.get.write(arg.toString)
                    else
                        processSession.get.write(NameConverter.nameWithAffix(arg.toString))
                }
                processSession.get.write(")))")
                processSession.get.write("\n")
                processSession.get.flush()
                
                val str = processSession.get.readLine()
                val value = str match {
                    case ProcessBuilderSolver.smt2Model(name, value) => value
                    case _ => Errors.Internal.impossibleState
                }
                smtValueToFortressValue(value, f.resultSort, smtValueToDomainElement)
            }

            override protected def evaluateFunction(f: FuncDecl, scopes: Map[Sort, Int]): Map[Seq[Value], Value] = {
                try {
                    // Get identifiers of all function parameters
                    val paramIdentifiers = for (i <- f.argSorts.indices) yield {
                        smtInterpTokens(f.name)(2 + i * 2)
                    }

                    // Set default value based on return sort
                    var defaultValue: Value = Bottom
                    f.resultSort match {
                        case BoolSort =>
                            if (smtInterpTokens(f.name).last.equals("true")) {
                                defaultValue = Top
                            }
                        case _ => defaultValue = smtValueToFortressValue(smtInterpTokens(f.name).last, f.resultSort, smtValueToDomainElement)
                    }
                    val interpMap: scala.collection.mutable.Map[Seq[Value], Value] = collection.mutable.Map({
                        for (argList <- ArgumentListGenerator.generate(f, scopes, Some(sortInterpretations)))
                            yield (argList -> defaultValue)
                    }.toMap.toSeq: _*)

                    // Parse the output based on either ite or plain boolean format
                    var index = smtInterpTokens(f.name).indexOf("ite")
                    if (index > -1 & smtInterpTokens(f.name)(index - 1) != "=") {
                        index = index - 1
                        while (index + 1 + f.argSorts.size * 3 < smtInterpTokens(f.name).length) {
                            // Using "ite" as an anchor
                            index = index + 1
                            // Get arguments
                            val argList = for (i <- f.argSorts.indices)
                                yield {
                                    index = index + 3
                                    // Handle the case of "(= value identifier)"
                                    var possibleParam = smtInterpTokens(f.name)(index)
                                    if (possibleParam.equals(paramIdentifiers(i))) possibleParam = smtInterpTokens(f.name)(index - 1)
                                    smtValueToFortressValue(possibleParam, f.argSorts(i), smtValueToDomainElement)
                                }
                            index = index + 1
                            // Get value and update interpretation map
                            interpMap.update(argList, smtValueToFortressValue(smtInterpTokens(f.name)(index), f.resultSort, smtValueToDomainElement))
                        }
                    } else if (index == -1 & smtInterpTokens(f.name).indexOf("or") > -1 & smtInterpTokens(f.name).indexOf("=") > -1) {
                        index = smtInterpTokens(f.name).indexOf("=") - 1
                        while (index + f.argSorts.size * 3 < smtInterpTokens(f.name).length) {
                            // Get arguments
                            val argList = for (x <- f.argSorts)
                                yield {
                                    index = index + 3
                                    smtValueToFortressValue(smtInterpTokens(f.name)(index), x, smtValueToDomainElement)
                                }
                            // Get value and update interpretation map
                            interpMap.update(argList, Top)
                        }
                    } else {
                        // Notice it is not necessarily in impossible state to get here, it
                        // is possible that default value has been correctly set. But we want
                        // to raise exception to be safe. It also handles other responses like
                        // "x!0" and "(and x!0 x!1)".
                        Errors.Internal.impossibleState
                    }
                    interpMap.toMap
                } catch {
                    case _: Throwable =>
                        // Fall back to the (get-value) approach
                        {
                            for (argList <- ArgumentListGenerator.generate(f, scopes, Some(sortInterpretations)))
                                yield argList -> evaluateFunctionByGetValue(f, argList)
                        }.toMap
                }
            }

            override protected def evaluateFunctionDefinition(): Set[FunctionDefinition] = {
                var model: String = "";
                processSession.get.write("(get-model)\n")
                processSession.get.flush()
                var line: String = processSession.get.readLine()
                while ({line = processSession.get.readLine(); line != ")"}) {
                    model ++= line + "\n"
                }
                val rawList: Either[Errors.ParserError, util.Set[FunctionDefinition]] = SmtModelParser.parse(model, smtValueToDomainElement.asJava);
                if (rawList.isLeft) {
                    throw new Exception(rawList.left.get.toString)
                }
                var funcList = rawList.right.get.asScala.toSet

//                funcList.foreach(i => {println(i.name)})

                funcList = {for(func <- funcList) yield func.copy(
                    name = NameConverter.nameWithoutAffix(func.name)
                )}.toSet
                funcList = funcList.filterNot(func => fortressNameToSmtValue.contains(func.name))

//                val funcNameSet: Set[String] = theory.get.signature.functionDeclarations.map(item => { item.name }).toSet

//                println("funcNameSet: " + funcNameSet)

//                funcList = funcList.filterNot(func => funcNameSet.contains(func.name) )


                println("Function Definitions: \n" + funcList.map(_.toString))

                funcList
            }

            // get sorts
            override protected def evaluateSort(sort: Sort): Seq[Value] = {
                smtValueToDomainElement.values.filter(
                    domainElement => domainElement.sort == sort
                ).toIndexedSeq
            }
        }
        Solution
    }

    private def getFortressNameToSmtValueMap(theory: Theory): Map[String, String] = {
        for (constant <- theory.constants) {
            processSession.get.write("(get-value (")
            processSession.get.write(NameConverter.nameWithAffix(constant.name))
            processSession.get.write("))")
        }
        processSession.get.write("\n")
        processSession.get.flush()
        
        (for(constant <- theory.constants) yield {
            val str = processSession.get.readLine()
            str match {
                case ProcessBuilderSolver.smt2Model(name, value) => {
                    Errors.Internal.assertion(constant.name == NameConverter.nameWithoutAffix(name), s""""${constant.name}" should be equal to "${NameConverter.nameWithoutAffix(name)}"""")
                    (constant.name -> value)
                }
                case _ => Errors.Internal.impossibleState
            }
        }).toMap
    }

    // transfer smt values to fortress values
    private def smtValueToFortressValue(
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
