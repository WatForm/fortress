package fortress.interpretation

import fortress.msfol._
import fortress.solvers._
import fortress.inputs._
import fortress.interpretation._
import fortress.modelfinders.{ErrorResult, ModelFinderResult}
import fortress.util._
import fortress.msfol._
import fortress.operations._

import scala.collection.mutable
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

class ParserBasedInterpretation(model: String, theory: Theory) extends Interpretation {

    protected def scopes: Map[Sort, Int] = for((sort, seq) <- sortInterpretations) yield (sort -> seq.size)

    // println("Model from z3: \n" + model + "\n")

    private val visitor: SmtModelVisitor = SmtModelParser.parse(model, theory.signature)
    private val rawFunctionDefinitions: mutable.Set[FunctionDefinition] = visitor.getFunctionDefinitions.asScala
    private val fortressName2SmtValue: mutable.Map[String, String] = visitor.getFortressName2SmtValue.asScala
    private val smtValue2DomainElement: mutable.Map[String, DomainElement] = visitor.getSmtValue2DomainElement.asScala

    // If a domain element isn't mentioned anywhere in the axioms, Z3 might fail to generate it.
    // Hack around this by patching any such cases back in.
    private val currentDEs = smtValue2DomainElement.values.toSet
    for (constant <- theory.constantDeclarations) {
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

    private def lookupSort(s: Sort): Seq[Value] = {
        smtValue2DomainElement.values.filter(
            domainElement => domainElement!=null && domainElement.sort == s
        ).toIndexedSeq
    }

    /** Maps a sort to a sequence of values. */
    override val sortInterpretations: Map[Sort, Seq[Value]] = {
        for(sort<-theory.signature.sorts) yield sort -> lookupSort(sort)
    }.toMap ++ (theory.signature.enumConstants transform ((_, v) => v.map(x => DomainElement.interpretName(x.name).get)))

    private def lookupConstant(c: AnnotatedVar): Value = {
        smtValueToFortressValue(
            fortressName2SmtValue(c.name), // H!val!0
            c.sort // H
        )
    }

    /** Maps a constant symbol to a value. */
    override val constantInterpretations: Map[AnnotatedVar, Value] = {
        for{
            c <- theory.signature.constantDeclarations
            if DomainElement.interpretName(c.name).isEmpty
        } yield (c -> lookupConstant(c))
    }.toMap

    // replace smt-value in function definition with fortress domainElements
    // eg: H!val!0 -> _@1H
    private def updateFunc(func: Term): Term = func match {
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

    override val functionDefinitions: Set[FunctionDefinition] = {
        val functionDefinitions = rawFunctionDefinitions.filter(item => {
            var flag: Boolean = false
            for (f <- theory.signature.functionDeclarations) {
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

    override val functionInterpretations: Map[FuncDecl, Map[Seq[Value], Value]] = Map.empty

    def smtValueToFortressValue(
         value: String, // H!val!0
         sort: Sort,   // H
    ): Value = sort match {
        case SortConst(_) => {
            if (smtValue2DomainElement.keySet.contains(value))
                smtValue2DomainElement(value)
            else
                DomainElement.interpretName(NameConverter.nameWithoutQuote(value)).get
        }
        case BoolSort => value match {
            case "true" => Top
            case "false" => Bottom
            case _ => Errors.Internal.impossibleState
        }
        case IntSort => value match {
            case ParserBasedInterpretation.negativeInteger(digits) => IntegerLiteral(-(digits.toInt))
            case ParserBasedInterpretation.negativeIntegerCondensed(digits) => IntegerLiteral(-(digits.toInt))
            case _ => IntegerLiteral(value.toInt)
        }
        /*
        case UnBoundedIntSort => value match {
            case ParserBasedInterpretation.negativeInteger(digits) => IntegerLiteral(-(digits.toInt))
            case ParserBasedInterpretation.negativeIntegerCondensed(digits) => IntegerLiteral(-(digits.toInt))
            case _ => IntegerLiteral(value.toInt)
        }
        */
        case BitVectorSort(bitwidth) => value match {
            case ParserBasedInterpretation.bitVecLiteral(radix, digits) => radix match {
                case "x" => BitVectorLiteral.ensureSignedValue(Integer.parseInt(digits, 16), bitwidth)
                case "b" => {
                    BitVectorLiteral.ensureSignedValue(Integer.parseInt(digits, 2),  bitwidth)
                }
                case _ => Errors.Internal.impossibleState
            }
            case ParserBasedInterpretation.bitVecExpr(digits, bitw) => {
                Errors.Internal.assertion(bitw.toInt == bitwidth)
                BitVectorLiteral(digits.toInt, bitwidth)
            }
            case ParserBasedInterpretation.bitVecExprCondensed(digits, bitw) => {
                Errors.Internal.assertion(bitw.toInt == bitwidth)
                BitVectorLiteral(digits.toInt, bitwidth)
            }
            case _ => Errors.Internal.impossibleState
        }
    }
}

object ParserBasedInterpretation {
    val smt2Model: Regex = """^\(\((\S+|\(.+\)) (\S+|\(.+\))\)\)$""".r
    val bitVecType: Regex = """\(_ BitVec (\d+)\)""".r
    val bitVecLiteral: Regex = """^#(.)(.+)$""".r
    val bitVecExpr: Regex = """\(_ bv(\d+) (\d+)\)""".r
    val bitVecExprCondensed: Regex = """(\d+)aaBitVecExpraa(\d+)""".r
    val negativeInteger: Regex = """\(- ?(\d+)\)""".r
    val negativeIntegerCondensed: Regex = """aaNegativeIntaa(\d+)""".r

    val  BitVectorLiteral: Regex = """BitVectorLiteral.+""".r
}