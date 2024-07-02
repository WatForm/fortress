package fortress.config

import fortress.compilers._
import fortress.modelfinders._
import fortress.operations._
import fortress.config._
import fortress.util._

/**
  * Used to create a compiler and modelfinder in combination.
  *
  */
class Manager {
    
    // The options
    protected val options: collection.mutable.Map[String, ConfigOption] = new collection.mutable.HashMap[String, ConfigOption]()

    // The number determining the order options are applied in. Lower applies first.
    protected val priorities: collection.mutable.Map[String, Float] = new collection.mutable.HashMap[String, Float]()

    /**
      * Adds a ConfigOption to the manager
      *
      * @param option The option to add
      * @param priority The priority it will be given
      */
    def addOption(option: ConfigOption, priority: Float = 5000.0f): Unit = {
        val optionName = option.name

        Errors.Internal.precondition(!(options contains optionName), f"Option '$optionName' already exists.")

        options(optionName) = option
        priorities(optionName) = priority
    }

    def removeOption(optionName: String): Unit = {
        Errors.Internal.precondition(options contains optionName, f"Option '$optionName' does not exist.")
        options remove optionName
        priorities remove optionName
    }

    def getOption(optionName: String): Option[ConfigOption] = options.get(optionName)

    def getOptionPath(path: Seq[String]): Option[ConfigOption] = {
      path match {
        // If the list is empty return
        case Nil => None
        // If the list has one element, make an attempt
        case head :: Nil => getOption(head)
        // Find the next step and make sure it is a group object
        case head :: tail => getOption(head) match {
          case Some(nextOption) if nextOption.isInstanceOf[GroupOption] =>
            nextOption.asInstanceOf[GroupOption].getOptionPath(tail)
          case _ => None
        }
      }
    }



    def setPriority(optionName: String, newPriority: Float): Unit = {
        Errors.Internal.precondition(priorities contains optionName, f"Option '$optionName' does not exist.")
        priorities(optionName) = newPriority
    }

    private def getOptionsByPriority(): Seq[ConfigOption] = {
        val allNames = options.keys.toSeq
        // Sort the names using the priorities
        val orderedNames = allNames.sortWith(priorities(_) < priorities(_))

        orderedNames.map(options(_))
    }

    def setupCompiler(): ConfigurableCompiler = {
        // Make a new compiler of the proper type
        val compiler = new ConfigurableCompiler()
        // Let each option modify the compiler
        getOptionsByPriority().foreach(_.modifyCompiler(compiler))
        // return the compiler
        compiler
    }

    //def setupModelFinder(): ConfigurableModelFinder = new ConfigurableModelFinder(this)

}

object Manager {
  def makeDefaultZero(): Manager = {
    var manager: Manager = new Manager
    manager.addOption(TypecheckSanitizeOption, 5001)
    manager.addOption(EnumEliminationOption, 5002)
    manager.addOption(NnfOption, 5003)
    // Space for symmetry breaking
    manager.addOption(QuantifierExpansionOption, 5501)
    manager.addOption(RangeFormulaOption, 5502)
    manager.addOption(SimplifyOption, 5503)
    manager.addOption(DatatypeOption, 5504)
    return manager
  }

  def makeEmpty(): Manager = new Manager
}
