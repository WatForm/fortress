package fortress.operations

import fortress.msfol._
import fortress.operations.TermOps._

/**
  * Renamer
  * 
  * renames all Vars and Function names found in the term
  * that are in the mapping to the new name 
  * given in the mapping
  * 
  * more general than termOps.renameApplication 
  * because this will do many renamings at once
  * Assumption: this renaming is safe because the names to 
  * be replaced have the same sorts
  */

class Renamer(renamings: Map[String, String]) extends NaturalTermRecursion {

    def rename(term: Term, boundVars:List[String] = List[String]()): Term = naturalRecur(term)

    // has to be a list of lists b/c
    // scopes may have the same var in them
    var boundVars:List[List[String]] = List[List[String]]()

    override val exceptionalMappings: PartialFunction[Term, Term] = {
        case Var(name) => {
            if (!(boundVars.flatten.contains(name)) &&
                (renamings.contains(name))) {
                Var(renamings.apply(name))
            } else {
                Var(name)
            }
        }
        case App(fname, args) => {
            // don't have to worry about bound vars here
            if (renamings.contains(fname)) {
                App(renamings.apply(fname), 
                    args.map(arg => rename(arg)))
            } else {
                App(fname, 
                    args.map(arg => rename(arg)))
            }
        }
        case Forall(vars, body) => {
            // we have to remove the bound vars from the
            // renamings temporarily
            boundVars = List(vars.map(_.name).toList) ++ boundVars 
            val x = Forall(vars, rename(body))
            boundVars = boundVars.tail
            x
        }
        case Exists(vars, body) => {
            boundVars = List(vars.map(_.name).toList) ++ boundVars 
            val x = Exists(vars, rename(body)) 
            boundVars = boundVars.tail
            x
        }
    }
}