/**
  * A transformer that takes two related problemStates (ps1 and ps2) and sets up
  * a problemState that is the result of merging and semantically
  * comparing them:
  * the resulting problemState is satisfiable by instances
  * statisfies ps1 but not ps2

  ProblemState Elements
  - theory
    - signature
      - sorts
      - constantDeclarations
      - functionDeclarations
      - constantDefinitions
      - functionDefinitions
    - axioms
  - scopes
  - skolemConstants
  - skolemFunctions
  - rangeRestrictions
  - unapply
  - flags

  */

package fortress.transformers

import fortress.util.Errors
import fortress.msfol._
import fortress.operations.EvaluationInliner
import fortress.operations.TheoryOps._
import fortress.problemstate.ProblemState
import scala.jdk.CollectionConverters._

/* these are all elements of a problemState:
  * @param theory the theory
  * @param scopes the scopes for the theory
  * @param skolemConstants introduced skolem constants
  * @param skolemFunctions introduced skolem functions
  * @param rangeRestrictions introduced range restrictions (these also exist as formulas within the theory)
  * @param unapplyInterp a LIFO stack of instructions (given as a LIFO stack of functions) that describe how to undo 
  *                      the transformations thus far when giving an interpretation back to the user 
  * @param distinctConstants ?
  * @param flags set to if a transformer has been run
  * @param verbose flag set to indicate output should be verbose
*/



class MergeTransformer (
    problemState2: ProblemState
) extends ProblemStateTransformer {

    val notDisjointMsg = "problemStates are not disjoint for MergeTransformer"
    val emptyTheoryMsg = "both theories are empty for MergeTransformer"

    override def apply(problemState1: ProblemState): ProblemState = {

      // general function to check for errors between two 
      // parts of the theory or problemState
      // returns merged set if no errors
      // raises exception if error
      def checkForMergeErrors[A,B]
        (thing:ProblemState => Set[A],
         attr:A => B, // what to match on
         test:(A,A) => Boolean // rest of object attributes to test
        ): Set[A] = {
        for (s1 <- thing(problemState1)) {
          val result = thing(problemState2).find(attr(_) == attr(s1))
          result match {
            case Some(s2) => 
              if (test(s1,s2))
                throw new Errors.UnsupportedFeature(notDisjointMsg)
            case _ => // if not found, not a problem
          }
        } 
        return (thing(problemState1) ++ thing(problemState2)).toSet
      }

      // theory: signature: sorts 
      // problemState: scopes
      // if same name, scopes must be the same      
      val newSorts = checkForMergeErrors(
        ((x:ProblemState) => x.theory.signature.sorts),  // Set[Sort]
        (x:Sort) => x.name,
        (x:Sort, y:Sort) => 
            x.isBuiltin != y.isBuiltin |
            // need this to be a lazy &&
            ((problemState1.scopes.keySet contains x) &&
             (problemState2.scopes.keySet contains y) &&
            problemState1.scopes(x).size != problemState2.scopes(y).size)   // comparing scopes
        )
      // also merge scopes
      val newScopes = problemState1.scopes ++ problemState2.scopes 

      // theory: signature: constantDeclarations
      // constant declarations are class Annotated Var 
      // if same name, must have same sort expression       
      val newConstantDeclarations = checkForMergeErrors(
        ((x:ProblemState) => x.theory.signature.constantDeclarations),
        (x:AnnotatedVar) => x.name,
        (x:AnnotatedVar, y:AnnotatedVar) => 
            x.sort != y.sort // compare the sort if they have the same name
        )

      // theory: signature: functionDeclarations
      // function declarations are class FuncDecl
      // if same name, must have same sort expression
      val newFunctionDeclarations = checkForMergeErrors(
        ((x:ProblemState) => x.theory.signature.functionDeclarations),
        (x:FuncDecl) => x.name,
        (x:FuncDecl, y:FuncDecl) => 
            x.argSorts != y.argSorts ||
            x.resultSort != y.resultSort
        )

      // theory: signature: constant definitions
      // constant definitions are class ConstantDefinition
      // definitions: if same name, must be same sort and body
      val newConstantDefinitions = checkForMergeErrors(
        ((x:ProblemState) => x.theory.signature.constantDefinitions),
        (x:ConstantDefinition) => x.name,
        (x:ConstantDefinition, y:ConstantDefinition) => 
            x != y
        )

      // theory: signature: function definitions
      // function definitions are class FunctionDefinition
      // definitions: if same name, must be same sort and body
      val newFunctionDefinitions = checkForMergeErrors(
        ((x:ProblemState) => x.theory.signature.functionDefinitions),
        (x:FunctionDefinition) => x.name,
        (x:FunctionDefinition, y:FunctionDefinition) => 
            x != y
        )

      // theory: signature: enumConstants
      // enumConstants: Map[Sort, Seq[EnumValue]]
      // if same sort name, must have same Seq[EnumValue]
      val newEnumConstants = checkForMergeErrors(
        ((x:ProblemState) => x.theory.signature.enumConstants.keySet),
        (x:Sort) => x.name,
        (x:Sort, y:Sort) => 
            problemState1.theory.signature.enumConstants(x) != problemState2.theory.signature.enumConstants(y)
        )      

      // theory: axioms
      // from theory1, just add all of its axioms (this means the conjunction of all of its axioms)
      // from theory2, create one disjunction of the negation of each axiom 
      if (problemState2.theory.axioms.size == 0 &&
         problemState1.theory.axioms.size == 0) {
         throw new Errors.UnsupportedFeature(emptyTheoryMsg)
        }
      var newAxioms2 =
        if (problemState2.theory.axioms.size > 1)  
          List(OrList(problemState2.theory.axioms.map(Not(_)).toSeq))
        else 
          // only one axiom
          problemState2.theory.axioms.map(Not(_))
      val newAxioms = problemState1.theory.axioms ++ newAxioms2

      val newTheory =
        Theory.empty
          .withSorts(newSorts.asJava:java.lang.Iterable[Sort])
          .withConstantDeclarations(newConstantDeclarations)
          .withFunctionDeclarations(newFunctionDeclarations)
          .withConstantDefinitions(newConstantDefinitions)
          .withFunctionDefinitions(newFunctionDefinitions)
          .withAxioms(newAxioms)

      // problem state: skolemConstants
      // skolemConstants:Set[AnnotatedVar]
      val newSkolemConstants = checkForMergeErrors(
        ((x:ProblemState) => x.skolemConstants),
        (x:AnnotatedVar) => x.name,
        (x:AnnotatedVar, y:AnnotatedVar) => 
            x.sort != y.sort // compare the sort if they have the same name
        )

      // problem state: skolemFunctions
      // skolemConstants:Set[FuncDecl]
      val newSkolemFunctions = checkForMergeErrors(
        ((x:ProblemState) => x.skolemFunctions),
        (x:FuncDecl) => x.name,
        (x:FuncDecl, y:FuncDecl) => 
            x.argSorts != y.argSorts ||
            x.resultSort != y.resultSort
        )

      // problem state: rangeRestrictions
      // rangeRestrictions:Set[RangeRestriction]
      val newRangeRestrictions = checkForMergeErrors(
        ((x:ProblemState) => x.rangeRestrictions),
        (x:RangeRestriction) => x.term,
        (x:RangeRestriction, y:RangeRestriction) => 
            x.values != y.values
        )

      // problem state: unapplyInterp
      // not quite sure what to do here???????
      // one list followed by the other
      // second unapplies may not be effective if first one
      // have already made the change?
      // we don't want the change to happen doubly though
      val newUnapplyInterp =
        problemState1.unapplyInterp ++ problemState2.unapplyInterp 

      // problem state: flags
      // must be identical
      if (problemState1.flags == problemState2.flags) {
        val newFlags = problemState1.flags.copy()
      } else {
        throw new Errors.UnsupportedFeature(notDisjointMsg)
      }

      ProblemState.empty
        .withTheory(newTheory)
      /*
      .withFlags(problemState.flags.copy(trivialResult = newTheory.checkTrivial))
      */
    }
}