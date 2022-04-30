package fortress.config

import fortress.compiler._
import fortress.modelfind._
import fortress.operations._
import fortress.config._
import fortress.util._

/**
  * Used to create a compiler and modelfinder in combitionation.
  *
  */
class Manager {
    
    // The options
    protected val options: collection.mutable.Map[String, ConfigOption] = new collection.mutable.HashMap[String, ConfigOption]()

    // The priority given for each option
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

    def getOption(optionName: String): ConfigOption = options(optionName)

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

}
