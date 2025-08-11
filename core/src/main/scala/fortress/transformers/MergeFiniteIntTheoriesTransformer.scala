/**
  * A transformer that takes two related problemStates (ps1 and ps2) and sets up
  * a problemState that is the result of merging and semantically
  * comparing them:
  * the resulting problemState is satisfiable by instances
  * statisfies ps1 but not ps2

  Assumptions
  - problemState.finiteInts is defined

  Notes:
  - this transformer MUST be kept in sync with the ProblemState/theory elements
 
  */

package fortress.transformers

import scala.collection.mutable
import scala.collection.mutable.Map
import scala.collection.mutable.ListBuffer
import fortress.util.Errors
import fortress.data.IntSuffixNameGenerator
import fortress.data.CartesianSeqProduct
import fortress.msfol._
import fortress.operations.EvaluationInliner
import fortress.operations.Renamer
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState
import fortress.problemstate.Scope
import scala.jdk.CollectionConverters._

class MergeFiniteIntTheoriesTransformer (
    problemState2: ProblemState
) extends ProblemStateTransformer {

    val notDisjointMsg = "problemStates are not disjoint for MergeTransformer: "
    val emptyTheoryMsg = "both theories are empty for MergeTransformer"

    override def apply(problemState1: ProblemState): ProblemState = {

      assert(problemState1.finiteInts.size == 1)
      assert(problemState2.finiteInts.size == 1)

      val finiteInts1 = problemState1.finiteInts.head
      val finiteInts2 = problemState2.finiteInts.head

      val intSort1 = finiteInts1.finiteIntSort
      val intSort2 = finiteInts2.finiteIntSort

      val toInt1 = finiteInts1.toInt
      val toInt2 = finiteInts2.toInt

      val fromInt1 = finiteInts1.fromInt
      val fromInt2 = finiteInts2.fromInt

      val minInt = finiteInts1.minInt
      val maxInt = finiteInts1.maxInt 

      assert(minInt == problemState2.finiteInts.head.minInt)
      assert(maxInt == problemState2.finiteInts.head.maxInt)

      // build up map of renamings throughout merging elements
      // later use these renamings for definition bodies and axioms
      // mutable b/c of import above
      val theory2renamings = Map.empty[String, String]
      // the following are a subset up the above
      // just for constant decls
      // and function decls b/c these two also need
      // axioms
      val theory2constantRenamings = Map.empty[String, String]
      val theory2functionRenamings = Map.empty[String, String]

      var nameGenerator = IntSuffixNameGenerator.restrictAllNamesInTheory(problemState1.theory)
      nameGenerator.forbidNames(problemState2.theory.collectAllNamesInTheory.toSet)

      /* 
       * simpleMerge
       *
       * merges two 'things' from problemStates if things are distinct 
       * throws an exception otherwise
       * no renamings ever required
       *
       * everything has to be 'set'-ified in the parameter functions
       */
      def simpleMerge[A](
        thing:ProblemState => Set[A],
        comp:(Set[A],Set[A]) => Boolean,
        ): Set[A] = {
          val diff1 = thing(problemState1) diff thing(problemState2)
          val diff2 = thing(problemState2) diff thing(problemState1)
          if (comp(diff1,diff2)) {
            throw new Errors.UnsupportedFeature(notDisjointMsg)
          } 
          thing(problemState1) ++ thing(problemState2)
        }

      /*
       * merge
       * 
       * check for errors between two 
       * parts of the theory or problemState
       * returns merged/renamed set if no errors
       * raises exception if something can't merge
       */
      
      def merge[A,B]
        (thing:ProblemState => Set[A],
         name:A => String,          // what to match on
         matchTest:(A,A) => Boolean, // rest of object attributes to test
         renamedThing:(String,A) => A, // how to create a new renamed object
         constantDecl:Boolean = false, // have to keep a separate list for axioms
         funcDecl:Boolean = false // have to keep a separate list for axioms
        ): Set[A] = {
          val thing1 = thing(problemState1)
          val thing2 = thing(problemState2)
          // split union into three sets
          // because we remove the identical things
          // in the loop below, we can be sure that if they match
          // on the attr, they are not identical overall
          val theSame = thing1.intersect(thing2)
          val diff1 = thing1.diff(theSame)
          // must be mutable
          val diff2:scala.collection.mutable.Set[A] = mutable.Set() ++ (thing2 -- theSame)
          // accumulator
          val result = mutable.Set() ++ theSame
          for (s1 <- diff1) {
            val r = diff2.find(name(_) == name(s1))
            // we know they are not identical 
            // b/c then they would be in "theSame"
            r match {
             case Some(s2) => 
                if (matchTest(s1,s2)) {
                  val newName = nameGenerator.freshName(name(s2))
                  theory2renamings(name(s2)) = newName
                  if (constantDecl) theory2constantRenamings(name(s2)) = newName
                  if (funcDecl) theory2functionRenamings(name(s2)) = newName
                  result.add(renamedThing(newName, s2))
                  diff2.remove(s2)
                } else {
                  throw new Errors.UnsupportedFeature(notDisjointMsg)
                }
             case _ => {
                // it's not in thing2
                result.add(s1)
              }
            }
          } 
          // result is immutable
          (result ++ diff2).toSet // add in the diff2's not found in diff1
      }
      
      /*
       * problemState.theory.signature.sorts 
       * no conflict possible b/c just sort names
       */  
      val newSorts = problemState1.theory.sorts ++ problemState2.theory.sorts

      /*
       * problemState: scopes
       * scopes are Map[Sort, Scope]
       * 
       * if same name, scopes must be the same, else fail 
       * no renaming here
       */ 
      
      val newScopes = simpleMerge(
        (_.scopes.toSet),
        (x:Set[(Sort,Scope)],y:Set[(Sort,Scope)]) => x.toMap.keySet.intersect(y.toMap.keySet).nonEmpty 
      )
     

      // a sort is considered equivalent in two theories
      // if they are the same sort OR
      // if each is using its own version of finiteInts
      def intSortCompare(s1:Sort, s2:Sort):Boolean = {
        return (s1 == s2 || s1 == intSort1 && s2 == intSort2)
      }

     /*
       * problemState.theory.signature.constantDeclarations
       * constant declarations are class Annotated Var 
       *
       * if same constant name, must have same sort expression 
       * except that sort for finite ints can be different
       * renaming possible here
       */
      val newConstantDeclarations = merge(
        _.theory.signature.constantDeclarations,
        (x:AnnotatedVar) => x.name,
        (x:AnnotatedVar, y:AnnotatedVar) => 
            intSortCompare(x.sort,y.sort), // compare the sort if they have the same name
        (newName:String, y:AnnotatedVar) => AnnotatedVar(Var(newName),y.sort),   // how to rebuild it
        true,
        false 
        )

    
      /*
       * ProblemState.theory.signature.functionDeclarations
       * function declarations are class FuncDecl
       *
       * if same name, must have same sort expression
       * except that sort for finite ints can be different
       * renaming possible here
       */
      val newFunctionDeclarations = merge(
        _.theory.signature.functionDeclarations,
        (x:FuncDecl) => x.name,
        (x:FuncDecl, y:FuncDecl) => 
            (x.argSorts :+ x.resultSort)
               .zip(y.argSorts :+ y.resultSort)
               .forall { case (a, b) => intSortCompare(a,b) },
        (newName:String, y:FuncDecl) => FuncDecl(newName,y.argSorts, y.resultSort), 
        false, 
        true
        )
      
      /*  
       * ProblemState.theory.signature.constantDefinitions
       * constant definitions are class ConstantDefinition
       *
       * if same name, must be 'equivalent' sort and body
       * renaming possible here
       */

      // TODO: check body to be same mod use of
      val tmpConstantDefinitions = merge(
        _.theory.signature.constantDefinitions,
        (x:ConstantDefinition) => x.name,
        (x:ConstantDefinition, y:ConstantDefinition) => 
            // TOCHECK: these might not have the same body because of toInt/fromInt
            intSortCompare(x.sort,y.sort) && x.body == y.body,
        (newName:String, y:ConstantDefinition) => ConstantDefinition(AnnotatedVar(Var(newName),y.sort),y.body)  
        )

      /*
       * ProblemState.theory.signature.functionDefinitions
       * function definitions are class FunctionDefinition
       *
       * if same name, must be 'equivalent' sort and body
       * renaming possible here
       */
      val tmpFunctionDefinitions = merge(
        _.theory.signature.functionDefinitions,
        (x:FunctionDefinition) => x.name,
        (x:FunctionDefinition, y:FunctionDefinition) => 
            // TOCHECK: these might not have the same body because of toInt/fromInt
            // skipping var names??
            (x.argSortedVar.map((x:AnnotatedVar)=>x.sort) :+ x.resultSort)
               .zip(y.argSortedVar.map((x:AnnotatedVar)=>x.sort) :+ y.resultSort)
               .forall { case (a, b) => intSortCompare(a,b) },
            (newName:String, y:FunctionDefinition) => FunctionDefinition(newName,y.argSortedVar,y.resultSort,y.body)
        )

      /*
       * ProblemState.theory.signature.enumConstants
       * enumConstants: Map[Sort, Seq[EnumValue]]
       *
       * if same sort name, must have same Seq[EnumValue]
       * no renaming here
       */
      val newEnumConstants = simpleMerge(
         _.theory.enumConstants.toSet,
        (x:Set[(Sort,Seq[EnumValue])],y:Set[(Sort,Seq[EnumValue])]) => 
           x.toMap.keySet.intersect(y.toMap.keySet).nonEmpty 
      )
      

      // collected all the possible renamings now
      // do renaming in constant/function definitions and axioms

      // must be made immutable
      val renamer = new Renamer(theory2renamings.toMap)

      val newConstantDefinitions =
        tmpConstantDefinitions
          .map(x => ConstantDefinition(x.avar,renamer.rename(x.body)))
      val newFunctionDefinitions =
        tmpFunctionDefinitions
          .map(x => FunctionDefinition(x.name, x.argSortedVar, x.resultSort, renamer.rename(x.body)))


      /*
       * ProblemState.theory.axioms
       *
       * from theory1, add all of its axioms (this means the conjunction of all of its axioms)
       * no renaming needed for theory1
       *
       * from theory2, create one disjunction of the negation of each axiom after renaming
       * all renamings are for theory2
       */
      if (problemState2.theory.axioms.size == 0 &&
         problemState1.theory.axioms.size == 0) {
         throw new Errors.UnsupportedFeature(emptyTheoryMsg)
        }

      var newAxioms2 =
        if (problemState2.theory.axioms.size > 1)  
          List(OrList(
            problemState2.theory.axioms
              .map((t:Term) => Not(renamer.rename(t)))
              .toSeq))
        else 
          // only one axiom
          problemState2.theory.axioms
              .map((t:Term) => Not(renamer.rename(t)))
              .toSeq

      // make a mutable set to add more axioms to later
      var newAxioms = 
        (problemState1.theory.axioms ++ newAxioms2).to(mutable.Set)

      
     /*
      * Add Axioms to relate renamed constant/fun decls
      */

 
      /* Constant Declarations
       * renamings have to all be of intSort
       */
      for (c1 <- theory2constantRenamings.keySet) {
        // axiom: toInt1(c) = toInt2(c2)
        val c2 = theory2constantRenamings(c1)
        newAxioms.add(
          Eq(
            App(toInt1,Seq(Var(c1))),
            App(toInt2,Seq(Var(c2)))))
      }

     /* FunctionDeclarations
      * f: fromInt1 * A -> fromInt1 in theory1 
      * f:ourInts * A -> ourInts in theory2
      * f in theory2 has been renamed above 
      * to something like: f2:ourInts * A -> ourInts 
      *
      * If "int" has a finite range
      * of -1 to 1 (given in the problemState), and 
      * A has a range of {a1, a2}, then we add the 
      * following to the axioms:
      * toInt1(f(fromInt1(-1),a1)) = toInt2(f2(fromInt2(-1),a1))
      * toInt1(f(fromInt1(-1),a2)) = toInt(f2(fromInt2(-1),a2))
      * toInt1(f(fromInt1(0),a1)) = toInt(f2(fromInt2(0),a1))
      * toInt1(f(fromInt1(0),a2)) = toInt(f2(fromInt2(0),a2))
      * toInt1(f(fromInt1(1),a1)) = toInt(f2(fromInt2(1),a1))
      * toInt1(f(fromInt1(1),a2)) = toInt(f2(fromInt2(1),a2))
      * Recall that this is after quantifiers have 
      * been expanded
      */
    
      for (f1 <- theory2functionRenamings.keySet) {
        val f2 = theory2functionRenamings(f1)
        val decl: FuncDecl = problemState1.theory.signature.queryFunctionDeclaration(f1) match {
            case None => throw Errors.Internal.impossibleState
            case Some(decl) => decl
        }
        // we already know the argSorts match 
        // except for finiteInts positions


        val rhsArgValuesList = ListBuffer.empty[List[Term]]
        val lhsArgValuesList = ListBuffer.empty[List[Term]]
        for (argSort <- decl.argSorts) {
            if (argSort == intSort1) {
                lhsArgValuesList +=
                   (minInt to maxInt).toList
                    .map(x => App(fromInt1,Seq(IntegerLiteral(x))))
                rhsArgValuesList +=
                  (minInt to maxInt).toList
                  .map(x => App(fromInt2, Seq(IntegerLiteral(x))))
            } else if (argSort == BoolSort) { 
              lhsArgValuesList += List(Top, Bottom)
              rhsArgValuesList += List(Top, Bottom)
            } else if (!argSort.isBuiltin) {
               val argValues = 
                 DomainElement.range(1 to problemState1.scopes(argSort).size,argSort)
                 .map(x => x.asSmtConstant).toList
               lhsArgValuesList += argValues
               rhsArgValuesList += argValues
            } else {
              ???
              // TODO: fix this for builtin sorts
            }
        }
        // creates a list of pairs (x,y)
        // where x is a lhs arg list
        // and y is a rhs arg list
        var zipped = 
          lhsArgValuesList.zip(rhsArgValuesList)
        for ((lhsArgs,rhsArgs) <- zipped) {
           if (decl.resultSort == intSort1) {
            newAxioms.add(
              Eq(
                App(toInt1, Seq(App(f1,lhsArgs))),
                App(toInt2, Seq(App(f2,rhsArgs)))))
           } else {
            newAxioms.add(
              Eq(
                App(f1,lhsArgs),
                App(f2,rhsArgs)))         
           }
        }
      }
          
      val newTheory =
        Theory.empty
          .withSorts(newSorts.asJava:java.lang.Iterable[Sort])
          .withConstantDeclarations(newConstantDeclarations)
          .withFunctionDeclarations(newFunctionDeclarations)
          .withConstantDefinitions(newConstantDefinitions)
          .withFunctionDefinitions(newFunctionDefinitions)
          .withAxioms(newAxioms.toSet)

      /*
       * Problem state.skolemConstants
       * skolemConstants:Set[AnnotatedVar]
       *
       * must be distinct (each skolemize transformer should have used fresh constants)
       */

      val newSkolemConstants = simpleMerge(
        _.skolemConstants,
        (x:Set[AnnotatedVar],y:Set[AnnotatedVar]) => 
           x.map(_.name).intersect(y.map(_.name)).nonEmpty 
        )

      /*
       * ProblemState.skolemFunctions
       * skolemFunctions:Set[FuncDecl]
       *
       * differences must have distinct names 
       */
      val newSkolemFunctions = simpleMerge(
        _.skolemFunctions,
        (x:Set[FuncDecl],y:Set[FuncDecl]) => 
           x.map(_.name).intersect(y.map(_.name)).nonEmpty 
        )

      /*
       * ProblemState.rangeRestrictions
       * rangeRestrictions:Set[RangeRestriction]
       * RangeRestriction has a term and values
       *
       * if same term, should have same values
       */
      val newRangeRestrictions = simpleMerge(
        _.rangeRestrictions,
        (x:Set[RangeRestriction],y:Set[RangeRestriction]) =>
            x.map(_.term).intersect(y.map(_.term)).nonEmpty
        )
      
      /*
       * ProblemState.unapplyInterp
       *
       * one list followed by the other
       * TOCHECK not certain this is correct
       *
       * second unapplies may not be effective if first one
       * have already made the change?
       * we don't want the change to happen doubly though
       */
      val newUnapplyInterp =
        problemState1.unapplyInterp ++ problemState2.unapplyInterp 

      /*
       * ProblemState.flags
       *
       * must be identical
       */
      if (problemState1.flags == problemState2.flags) {
        val newFlags = problemState1.flags.copy()
      } else {
        throw new Errors.UnsupportedFeature(notDisjointMsg)
      }
      
      // TODO: merge finiteInts
      // make it a Set of finiteInts in the ProblemState

      ProblemState.empty
        .withTheory(newTheory)
        .withSkolemConstants(newSkolemConstants)
        .withSkolemFunctions(newSkolemFunctions)
        .withRangeRestrictions(newRangeRestrictions)
        .withUnapplyInterps(newUnapplyInterp)
        .addFiniteInts(finiteInts1)
        .addFiniteInts(finiteInts2)
        .withFlags(problemState1.flags)
 
    }
}