package fortress.transformers

import fortress.problemstate.ProblemState
import fortress.msfol._
import fortress.transformers.Polarity
import fortress.operations.LiaChecker

import fortress.operations.TermOps._
import fortress.interpretation.Interpretation

object MJUnknownsTransformer extends ProblemStateTransformer {

  def apply(problemState: ProblemState): ProblemState = {
    val oldTheory = problemState.theory

    // Run through definitions to get their overflows
    val defOverflows: scala.collection.mutable.Map[String, Result] =
      scala.collection.mutable.Map.empty

    var newSig = oldTheory.signature
    // We eliminate definitions with predicates in them, so we can determine which are univ/ext later
    // We just keep them in the upinfo for ease of use
    for (defn <- newSig.definitionsInDependencyOrder) {
      defn match {
        case Left(cdef) => {
          newSig = newSig.withoutConstantDefinition(cdef)
          val result = fixOverflow(cdef.body, newSig, MJStore.Nil)
          // the new definition uses the results cleaned term
          newSig = newSig.withConstantDefinition(cdef.copy(body = result.term))
          defOverflows.addOne(cdef.name -> result)
        }
        case Right(fDef) => {
          newSig = newSig.withoutFunctionDefinition(fDef)

          val sigWithArgs = newSig.withConstantDeclarations(fDef.argSortedVar)
          val result = fixOverflow(fDef.body, sigWithArgs, MJStore.Nil)
          newSig = newSig.withFunctionDefinition(fDef.copy(body = result.term))
        }
      }
    }

    var allDeclaredAvars = Set.empty[AnnotatedVar]
    val newAxioms = oldTheory.axioms.map((axiom) => {
      val result = fixOverflow(axiom, newSig, MJStore.Nil)

      val declaredAvars = result.declaredVars.map(AnnotatedVar(_, BoolSort))
      allDeclaredAvars ++= declaredAvars
      newSig = newSig.withConstantDeclarations(declaredAvars)

      result.term
    })

    val newTheory = Theory(newSig, newAxioms)

    def unapply(i: Interpretation): Interpretation = {
      i.withoutConstants(allDeclaredAvars)
    }

    problemState
      .withTheory(newTheory)
      .addUnapplyInterp(unapply)
  }

  def fixOverflow(term: Term, sig: Signature, store: MJStore): Result =
    term match {
      case Var(x) => {
        Result(term, UpInfo.withVar(Var(x)), Set.empty)
      }

      case _: LeafTerm => Result(term, UpInfo.empty, Set.empty)

      case BuiltinApp(function: BinaryBitVectorRelation, arguments) => {
        val originalLeft = arguments(0)
        val originalRight = arguments(1)
        val left = fixOverflow(originalLeft, sig, store)
        val right = fixOverflow(originalRight, sig, store)

        val newFunc = BuiltinApp(function, left.term, right.term)
        val newUp = left.info.merge(right.info)

        var newDefns = left.declaredVars ++ right.declaredVars

        val (checkedFunc, newDefn) =
          ensureDefn(newFunc, store, left.info, right.info)

        newDefn match {
          case None    => ()
          case Some(d) => newDefns = newDefns + d
        }

        Result(checkedFunc, newUp, newDefns)
      }

      // TODO can this case handle predicates?
      case BuiltinApp(function, arguments) => {
        val results = arguments.map(fixOverflow(_, sig, store))

        val cleanArgs = results.map(_.term)
        val newTerm = BuiltinApp(function, cleanArgs)

        // Gather checks
        var newUp = UpInfo.merge(results.map(_.info))

        results.foreach((result) => {
          IntNOBVTransformer.overflowCheck(result.term, sig) match {
            case None => ()
            case Some(newCheck) => {
              newUp = newUp.withCheck(newCheck)
            }
          }
        })

        // Combine polarityConstants
        val newPCs = results.map(_.declaredVars).fold(Set.empty)(_ union _)

        // Else we return the cleaned term
        return Result(newTerm, newUp, newPCs)
      }

      case Forall(avars, body) => {
        val newSig = sig.withConstantDeclarations(avars)

        // We don't care if polarity is indeterminant
        val q =
          if (MJStore.getPolarity(store) != Polarity.Negative)
            Quantification.Universal
          else Quantification.Existential
        // Polarity does not change
        val p = MJStore.getPolarity(store)

        // TODO do we include non-Int vars because we have uninterpreted functions
        // that map sort A to Int?
        var newStore = store
        for (av <- avars) {
          av.sort match {
            case BitVectorSort(bitwidth) => {
              newStore = MJStore.Some(av.variable, q, p, newStore)
            }
            // TODO option to include non-boolean vars
            case _ => ()
          }
        }

        val res = fixOverflow(body, newSig, newStore)

        val newTerm = Forall(avars, res.term)
        val newInfo = res.info.withoutVars(avars.map(_.variable).toSet)

        Result(newTerm, newInfo, res.declaredVars)
      }

      case Exists(avars, body) => {
        val newSig = sig.withConstantDeclarations(avars)

        // We don't care if polarity is indeterminant
        val q =
          if (MJStore.getPolarity(store) != Polarity.Negative)
            Quantification.Existential
          else Quantification.Universal
        // Polarity does not change
        val p = MJStore.getPolarity(store)

        // TODO do we include non-Int vars because we have uninterpreted functions
        // that map sort A to Int?
        var newStore = store
        for (av <- avars) {
          av.sort match {
            case BitVectorSort(bitwidth) => {
              newStore = MJStore.Some(av.variable, q, p, newStore)
            }
            // TODO option to include non-boolean vars
            case _ => ()
          }
        }

        val res = fixOverflow(body, newSig, newStore)

        val newTerm = Exists(avars, res.term)
        val newInfo = res.info.withoutVars(avars.map(_.variable).toSet)

        Result(newTerm, newInfo, res.declaredVars)
      }

      case Closure(fname, arg1, arg2, fixedArgs) => {
        val newStore = store.withPolarity(Polarity.Indeterminate)
        val res1 = fixOverflow(arg1, sig, newStore)
        val res2 = fixOverflow(arg2, sig, newStore)
        val fixedResults = fixedArgs.map(fixOverflow(_, sig, newStore))

        val newTerm =
          Closure(fname, res1.term, res2.term, fixedResults.map(_.term))
        val newInfo =
          UpInfo.merge(Seq(res1.info, res2.info) ++ fixedResults.map(_.info))

        val newDeclared = res1.declaredVars ++ res2.declaredVars ++ fixedResults
          .map(_.declaredVars)
          .fold(Set.empty)(_ union _)

        Result(newTerm, newInfo, newDeclared)
      }

      case ReflexiveClosure(fname, arg1, arg2, fixedArgs) => {
        val newStore = store.withPolarity(Polarity.Indeterminate)
        val res1 = fixOverflow(arg1, sig, newStore)
        val res2 = fixOverflow(arg2, sig, newStore)
        val fixedResults = fixedArgs.map(fixOverflow(_, sig, newStore))

        val newTerm = ReflexiveClosure(
          fname,
          res1.term,
          res2.term,
          fixedResults.map(_.term)
        )
        val newInfo =
          UpInfo.merge(Seq(res1.info, res2.info) ++ fixedResults.map(_.info))

        val newDeclared = res1.declaredVars ++ res2.declaredVars ++ fixedResults
          .map(_.declaredVars)
          .fold(Set.empty)(_ union _)

        Result(newTerm, newInfo, newDeclared)
      }

      case Eq(left, right) => {
        val sort = left.typeCheck(sig).sort

        sort match {
          case BoolSort => {
            // Turn into l <==> r
            fixOverflow(Iff(left, right), sig, store)
          }
          case BitVectorSort(bitwidth) => {
            val resLeft = fixOverflow(left, sig, store)
            val resRight = fixOverflow(right, sig, store)
            val (checkedTerm, declaredVars) =
              ensureDefn(Eq(left, right), store, resLeft.info, resRight.info)

            val newInfo = UpInfo.merge(Seq(resLeft.info, resRight.info))
            val newDeclared =
              resLeft.declaredVars ++ resRight.declaredVars ++ declaredVars
            // No checks up from here
            Result(checkedTerm, newInfo.withoutChecks(), newDeclared)
          }

          case _ => {
            // Non-integer predicate
            // TODO what if it contains integer overflows?
            // I think not. The problem with not knowing polarity is here
            // Just treat as uninterpreted function

            val newStore = store.withPolarity(Polarity.Indeterminate)
            val resLeft = fixOverflow(left, sig, newStore)
            val resRight = fixOverflow(right, sig, newStore)

            Result.merge((i) => Eq(i.head, i.tail.head), resLeft, resRight)
          }
        }
      }

      case Iff(left, right) => {
        val split = Or(And(left, right), And(Not(left), Not(right)))
        fixOverflow(split, sig, store)
      }

      case Implication(left, right) =>
        fixOverflow(Or(Not(left), right), sig, store)

      case AndList(arguments) => {
        val results = arguments.map(fixOverflow(_, sig, store))
        Result.merge((terms) => AndList(terms.toSeq), results: _*)
      }

      case OrList(arguments) => {
        val results = arguments.map(fixOverflow(_, sig, store))
        Result.merge((terms) => OrList(terms.toSeq), results: _*)
      }

      case Not(body) => {
        val newStore = store.withPolarity(Polarity.flip(store.getPolarity()))
        val innerResult = fixOverflow(body, sig, newStore)
        innerResult.copy(term = Not(innerResult.term))
      }

      case Distinct(arguments) => {
        val sort = arguments.head.typeCheck(sig).sort

        sort match {
          case BoolSort => {
            arguments match {
              case Nil => ???
              case _ :: Nil =>
                Result(Top, UpInfo.empty, Set.empty) // distinct from self
              case left :: right :: Nil =>
                fixOverflow(Iff(left, right), sig, store)
              case _ =>
                Result(Bottom, UpInfo.empty, Set.empty) // 3 cannot be distinct
            }
          }
          case BitVectorSort(bitwidth) => {
            val newStore = store.withPolarity(Polarity.Indeterminate)
            val results = arguments.map(fixOverflow(_, sig, newStore))

            val unchecked = Distinct(results.map(_.term))
            val (checkedTerm, declaredVars) =
              ensureDefn(unchecked, store, results.map(_.info): _*)

            val initialDeclared = Set.from(declaredVars)

            // We know what the checkedTerm will be
            val newInfo = UpInfo.merge(results.map(_.info))
            val newDeclared =
              results.map(_.declaredVars).fold(initialDeclared)(_ union _)

            Result(checkedTerm, newInfo, newDeclared)
          }
          case _ => {
            // Non-integer predicate
            // TODO what if it contains integer overflows?
            // I think not. The problem with not knowing polarity is here
            // Just treat as uninterpreted function
            val newStore = store.withPolarity(Polarity.Indeterminate)
            val results = arguments.map(fixOverflow(_, sig, newStore))

            Result.merge((i) => Distinct(i.toSeq), results: _*)
          }
        }
      }

      case IfThenElse(cond, branchT, branchF) => {
        val conditionResult = fixOverflow(cond, sig, store)
        val branchTResult = fixOverflow(branchT, sig, store)
        val branchFResult = fixOverflow(branchF, sig, store)

        // TODO what if ITE is of bool sort?
        // Should this be handled already
        val newTerm = IfThenElse(
          conditionResult.term,
          branchTResult.term,
          branchFResult.term
        )
        val newInfo = UpInfo.merge(
          Seq(conditionResult.info, branchTResult.info, branchFResult.info)
        )
        val newDeclaredVars =
          conditionResult.declaredVars ++ branchTResult.declaredVars ++ branchFResult.declaredVars

        Result(newTerm, newInfo, newDeclaredVars)
      }

      case App(fname, args) => {
        var argSorts: Seq[Sort] = Seq.empty
        var resultSort: Sort = BoolSort
        sig.queryFunction(fname) match {
          case None => ???
          case Some(func) => func match {
            case Left(fdecl) => {
              argSorts = fdecl.argSorts
              resultSort = fdecl.resultSort
            }
            case Right(fdef) => {
              argSorts = fdef.argSorts
              resultSort = fdef.resultSort
            } 
          }
        }

        val argResults = args.map(fixOverflow(_, sig, store))


        // If boolsort...
        // Otherwise...
        resultSort match {
          case BoolSort => {
            val uncheckedTerm = App(fname, argResults.map(_.term))
            val (checkedTerm, newDecl) = ensureDefn(uncheckedTerm, store, argResults.map(_.info):_*)
            
            //DO NOT push checks up
            val newUp = UpInfo.merge(argResults.map(_.info))
            .withoutChecks()

            val argDecls = argResults.map(_.declaredVars)
            val allDecls = argDecls.fold(newDecl.toSet)(_ union _)
            Result(checkedTerm, newUp, allDecls)
          }
          case _ => {
            Result.merge((terms)=> App(fname, terms.toSeq), argResults:_*)
          }
        }
      }

      case Exists2ndOrder(declarations, body) => ???
      case Forall2ndOrder(_, _)               => ???

    }

  // ensureDefn adds
  def ensureDefn(
      uncheckedTerm: Term,
      store: MJStore,
      infos: UpInfo*
  ): (Term, Option[Var]) = {
    val (upUnivs, upExts) = infos.partition(_.isUnivQuant(store))

    val bDef =
      if (upExts.isEmpty)
        (Top)
      else {
        val upExtChecks = upExts
          .map(_.checks)
          .fold(Set.empty)(_ union _)
          .toSeq
        AndList(upExtChecks.map(Not(_)))
      }
    val bUndef =
      if (upUnivs.isEmpty)
        (Bottom)
      else {
        val upUnivChecks = upUnivs
          .map(_.checks)
          .fold(Set.empty)(_ union _)
          .toSeq
        OrList(upUnivChecks.map(Not(_)))
      }

    var declaredVar: Option[Var] = None
    val checkedTerm = MJStore.getPolarity(store) match {
      case Polarity.Positive => {
        // b or bundef
        val inner = if (bUndef == Top) Top else Or(uncheckedTerm, bUndef)
        if (bDef == Bottom) Bottom else And(inner, bDef)
      }
      case Polarity.Negative => {
        val inner = if (bDef == Bottom) Top else Or(uncheckedTerm, Not(bDef))
        if (bUndef == Top) Bottom else And(inner, Not(bUndef))
      }
      case Polarity.Indeterminate => {
        // If anything overflows, who knows
        // If nothing overflows, uncheckedTerm

        // TODO fresh variable!
        val polarityConstant = Var("!!MAKE A FRESH VAR!!")
        declaredVar = Some(polarityConstant)

        val allChecks = infos.map(_.checks).fold(Set.empty)(_ union _)

        if (allChecks.isEmpty) uncheckedTerm
        else {
          val overflows = OrList(allChecks.toSeq)

          Or(
            And(overflows, polarityConstant),
            And(Not(overflows), uncheckedTerm)
          )
        }
      }
    }

    (checkedTerm, declaredVar)
  }

}

sealed abstract class Quantification
object Quantification {
  case object Universal extends Quantification
  case object Existential extends Quantification
}

sealed abstract class MJStore {
  def getPolarity(): Polarity.Polarity
  def withPolarity(newP: Polarity.Polarity): MJStore
}
object MJStore {
  case object Nil extends MJStore {
    def getPolarity(): Polarity.Polarity = Polarity.Positive
    // TODO name generator
    def withPolarity(newP: Polarity.Polarity): MJStore =
      Some(Var("!!!FAKE!!!"), Quantification.Existential, newP, Nil)
  }
  // TODO make sure we start with a some of some kind for the polarity? Fake var?
  // Seems strange
  case class Some(
      x: Var,
      q: Quantification,
      p: Polarity.Polarity,
      tail: MJStore
  ) extends MJStore {
    def withPolarity(newP: Polarity.Polarity): MJStore = {
      Some(x, q, newP, tail)
    }

    def getPolarity(): Polarity.Polarity = p
  }

  def getPolarity = (_: MJStore) match {
    case Nil              => Polarity.Positive
    case Some(_, _, p, _) => p
  }
}

case class Result(term: Term, info: UpInfo, declaredVars: Set[Var])
object Result {
  def merge(termMerge: (Iterable[Term]) => Term, results: Result*): Result = {
    val resultTerms = results.map(_.term)

    val newTerm = termMerge(resultTerms)

    val newInfo = UpInfo.merge(results.map(_.info))

    val newPC = results.map(_.declaredVars).fold(Set.empty)(_ union _)

    Result(newTerm, newInfo, newPC)
  }
}

case class UpInfo(vars: Set[Var], checks: Set[Term]) {
  def withVar(v: Var): UpInfo = copy(vars = vars + v)

  def merge(other: UpInfo): UpInfo = {
    UpInfo(
      vars = vars.union(other.vars),
      checks = checks.union(other.checks)
    )
  }

  def isUnivQuant(store: MJStore): Boolean = store match {
    case MJStore.Nil => false
    case MJStore.Some(x, q, _, tailStore) => {
      if (vars contains x)
        (q == Quantification.Universal)
      else isUnivQuant(tailStore)
    }
  }

  def withCheck(check: Term): UpInfo = {
    copy(checks = checks + check)
  }

  def withoutVars(vs: Set[Var]): UpInfo = {
    val newVars = vars diff vs
    // Should probably not have any checks at this level for MJ?
    def doesNotContainVs(check: Term): Boolean = {
      val checkVars = check.freeVarConstSymbolsJava
      for (v <- vs) {
        if (checkVars contains v) {
          return false
        }
      }
      return true
    }

    val newChecks = checks.filter(doesNotContainVs)

    UpInfo(newVars, newChecks)
  }

  def withoutChecks(): UpInfo = copy(checks = Set.empty)
}
object UpInfo {
  val empty = UpInfo(Set.empty, Set.empty)

  def withVar(v: Var): UpInfo = empty.withVar(v)

  def merge(infos: Seq[UpInfo]): UpInfo = {
    infos.fold(empty)(_ merge _)
  }
}
