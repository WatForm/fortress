package fortress.symmetry

import fortress.msfol._

import scala.collection.mutable

/** Tracks the remaining constants, functions and predicates that we haven't
  * added any symmetry breaking constraints for
  */
class RemainingIdentifiersTracker private(
                                           remainingConsts: mutable.Set[AnnotatedVar],
                                           remainingFps: mutable.Set[FuncDecl]
                                         ) {

    val remainingConstants: mutable.Set[AnnotatedVar] = remainingConsts
    val remainingFuncDecls: mutable.Set[FuncDecl] = remainingFps

    // Marks constants as used
    def markUsedConstants(consts: AnnotatedVar*): Unit = {
        for (con <- consts) {
            remainingConstants.remove(con)
        }
    }

    // Marks constants as used
    def markUsedFuncDecls(funcDecls: FuncDecl*): Unit = {
        for (funcDecl <- funcDecls) {
            remainingFuncDecls.remove(funcDecl)
        }
    }
}


object RemainingIdentifiersTracker {
    def create(remainingConstants: Set[AnnotatedVar], remainingFuncDecls: Set[FuncDecl]): RemainingIdentifiersTracker = {
        new RemainingIdentifiersTracker(mutable.Set(remainingConstants.toSeq: _*), mutable.Set(remainingFuncDecls.toSeq: _*))
    }
}
