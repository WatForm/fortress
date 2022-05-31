package fortress.solverinterface

import scala.util.{Try,Success,Failure}

import com.microsoft.z3;

import fortress.msfol._
import fortress.util.Errors
import fortress.util.NameConverter._
import fortress.modelfind.ModelFinderResult
import fortress.util.Milliseconds
import fortress.interpretation.Interpretation

class Z3ApiSolver extends SolverSession {
    protected var theory: Option[Theory] = None

    protected var ctx: z3.Context = null
    protected var solver: z3.Solver = null

    protected var sortConsts: Map[String, z3.Sort] = Map()
    protected var constants: Map[String, z3.Expr[z3.Sort]] = Map()
    protected var funcdecls: Map[String, z3.FuncDecl[z3.Sort]] = Map()
    protected var symbols: Map[String, z3.Symbol] = Map()

    protected var quantifierCount: Int = 0
    protected var skolemizationIdCount: Int = 0

    override def setTheory(theory: Theory): Unit = {
        reset()
        // reset theory
        this.theory = Some(theory)
        // clear stuff
        ctx = new z3.Context()
        sortConsts = sortConsts.empty
        // Add uninterpreted sorts
        theory.sorts.foreach(_ match {
            case SortConst(name) => {
                sortConsts = sortConsts + (name -> ctx.mkUninterpretedSort(name))
            }
            case _ => {}
        })
        // Add enum sorts
        theory.enumConstants.keys.foreach(enumSortFortress => {
            val enumName = enumSortFortress.name
            val valueNames = theory.enumConstants(enumSortFortress).map(_.name)
            val sort = ctx.mkEnumSort(enumName, valueNames:_*) // :_* unpacks for the call to a function with varargs 
            sortConsts = sortConsts.updated(enumName, sort)
        })
        // Add constants
        constants = constants.empty
        theory.constants.foreach(_ match {
            case AnnotatedVar(variable, sortFortress) => {
                val constName: String = variable.name
                val sort = sortConsts(sortFortress.name)
                // We make the const in her to maintain typing (probably could be cleaned up but idk how)
                constants = constants.updated(constName, mkConst(constName, sort))
            }
        })
        // Add function Declarations
        funcdecls = funcdecls.empty
        theory.functionDeclarations.foreach(_ match {
            case FuncDecl(name, argsFortress, targetSortFortress) => {
                val args = argsFortress.map(x => sortConsts(x.name)).toArray
                val targetSort = sortConsts(targetSortFortress.name)
                val d = targetSort match {
                    case target: z3.EnumSort[r] => ctx.mkFuncDecl[z3.EnumSort[r]](name, args, target)
                    case target: z3.IntSort => ctx.mkFuncDecl[z3.IntSort](name, args, target)
                    case target: z3.BoolSort => ctx.mkFuncDecl[z3.BoolSort](name, args, target)
                }
                val decl = ctx.mkFuncDecl[z3.Sort](name, args, targetSort)
                funcdecls = funcdecls.updated(name, decl)
            }
        })



    }

    private def reset(): Unit = {
        sortConsts = sortConsts.empty
        constants = constants.empty
        funcdecls = funcdecls.empty
        symbols = symbols.empty

    }

    /*
     * Wrappers for typedness
     */ 
    def mkConst[S <: z3.Sort](name: String, sort: S): z3.Expr[S] = {
        ctx.mkConst[S](name, sort)
    }

    def mkApp[S <: z3.Sort](funcDecl: z3.FuncDecl[S], args: Seq[z3.Expr[_ <: Object]]) = {
        ctx.mkApp[S](funcDecl, args:_*)
    }

    // TODO improve matching
    // Maybe make this a PartialFunction

    def compileBoolExpr(term: Term): Try[z3.BoolExpr] = Try{
        term match {
            // Constant values
            case Bottom => ctx.mkFalse()
            case Top => ctx.mkTrue()
            // Ands and Ors
            case AndList(arguments) => {
                val args: Seq[z3.BoolExpr] = arguments.map(compileBoolExpr(_).get)
                ctx.mkAnd(args:_*)
            }
            case OrList(arguments) => {
                val args: Seq[z3.BoolExpr] = arguments.map(compileBoolExpr(_).get)
                ctx.mkOr(args:_*)
            }
            // Probably not typesafe. Could use a check
            case App(functionName, arguments) => Errors.API.wrongTypeError("Got App expected BoolExpr")

            case Eq(left, right) => ctx.mkEq(compileExpr(left), compileExpr(right))

            // Quantifiers
            case Exists(vars, bodyTerm) => {
                var varNamesAndSorts: (Seq[String], Seq[Sort]) = vars.map(unpackAnnotatedVar(_)).unzip
                var varNames = varNamesAndSorts._1
                var symbols = varNames.map(getSymbol)
                var sorts: Seq[z3.Sort] = varNamesAndSorts._2.map(getSort) // Translates to z3 Sorts
                var body = compileBoolExpr(bodyTerm).get

                // TODO add trackers (or patterns?)
                ctx.mkExists(sorts.toArray, symbols.toArray, body, 0, null, null, null, null)
            }

            case Forall(vars, bodyTerm) => {
                var varNamesAndSorts: (Seq[String], Seq[Sort]) = vars.map(unpackAnnotatedVar(_)).unzip
                var varNames = varNamesAndSorts._1
                var symbols = varNames.map(getSymbol)
                var sorts: Seq[z3.Sort] = varNamesAndSorts._2.map(getSort) // Translates to z3 Sorts
                var body = compileBoolExpr(bodyTerm).get

                // TODO add trackers (or patterns?)
                ctx.mkForall(sorts.toArray, symbols.toArray, body, 0, null, null, null, null)
            }
            
        }
    }

    /**
      * Gets the Name and Sort from an Annotated Var
      *
      * @param av the Annotated var to unpack
      * @return name, sort
      */
    protected def unpackAnnotatedVar(av: AnnotatedVar): (String, Sort) = av match {
        case AnnotatedVar(variable, sort) =>(variable.name, sort)
    }

    /**
      * Gets the proper symbol for the given name. Creates it if it is missing
      *
      * @param name the name of the symbol to find
      * @return the symbol representing the given identifier `name`
      */
    protected def getSymbol(name: String): z3.Symbol = {
        if (symbols contains name){
            symbols(name)
        } else {
            symbols = symbols.updated(name, ctx.mkSymbol(name))
            symbols(name)
        }
    }

    protected def getSort(sort: Sort): z3.Sort = {
        sort match {
            case BoolSort => ctx.mkBoolSort()
            case IntSort => ctx.mkIntSort()
            case BitVectorSort(bitwidth) => ctx.mkBitVecSort(bitwidth)
            case SortConst(name) => {
                if (sortConsts contains name){
                    sortConsts(name)
                } else {
                    Errors.API.missingSortError("Unable to find sort '"+ name +"'")
                }
            } 
        }
    }

    protected def compileExpr(term: Term): z3.Expr[_ <: Object] = {
        // TODO
        ctx.mkTrue()
    }
    override def addAxiom(axiom: Term): Unit = {
        // Errors
    }

    override def solve(timeoutMillis: Milliseconds): ModelFinderResult = {
        ModelFinderResult.Unknown
    }

    override def solution: Interpretation = {
        object DummyInterp extends Interpretation {
            def constantInterpretations: Map[AnnotatedVar,Value] = Map()
            def functionInterpretations: Map[FuncDecl,Map[Seq[Value],Value]] = Map()
            def sortInterpretations: Map[Sort,Seq[Value]] = Map()
        }
        DummyInterp
    }

    override def close(): Unit = {}
}