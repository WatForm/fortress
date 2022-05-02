package fortress.config

import fortress.compiler.ConfigurableCompiler
import fortress.util.Errors
import java.io.ObjectInputFilter.Config

/**
  * An option for a compiler.
  * Essentially, an action to be taken when building the compiler.
  *
  * @param optionName
  * @param action
  */
class ConfigOption(optionName: String, action: ConfigurableCompiler => () = (_ => ())) {

  val name = optionName
  /**
    * Function to modify a configurable compiler based on the option.
    * This can be overridden for different option behavior (not for what the option changes)
    * @param compiler
    */
  def modifyCompiler(compiler: ConfigurableCompiler): Unit = {
    compilerModification(compiler)
  }

  /**
    * The behavior to modify the compiler.
    *
    * @param compiler
    */
  def compilerModification(compiler: ConfigurableCompiler): Unit = action(compiler)


}

/**
  * An option which will only activate while it is enabled
  *
  * @param name
  * @param defaultValue true if the option should start enabled
  */
class ToggleOption(optionName: String, action: ConfigurableCompiler => () = (_ => ()), defaultState: Boolean = true) extends ConfigOption(optionName, action) {
  protected var enabled: Boolean = defaultState

  def isEnabled() = enabled

  def enable() = {
    enabled = true
  }

  def disable() = {
    enabled = false
  }


  override def modifyCompiler(compiler: ConfigurableCompiler): Unit = {
    if (enabled) {
      compilerModification(compiler)
    }
  }

}


class GroupOption(optionName: String) extends ConfigOption(optionName) {
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

    def addOptionsWithPriority(prioritizedOptions: Seq[(ConfigOption, Float)]): Unit = {
      for ((option, priority) <- prioritizedOptions) {
        addOption(option, priority)
      }
    }

    def addOptions(newOptions: Seq[ConfigOption]): Unit = {
      for (option <- newOptions){
        addOption(option)
      }
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

    override def compilerModification(compiler: ConfigurableCompiler) = {
      // apply each option to the compiler
      getOptionsByPriority().foreach(_.modifyCompiler(compiler))
    }
    
}

class ToggleGroupOption(optionName: String, defaultState: Boolean = true) extends GroupOption(optionName) {
  protected var enabled: Boolean = defaultState

  def isEnabled() = enabled

  def enable() = {
    enabled = true
  }

  def disable() = {
    enabled = false
  }

  override def compilerModification(compiler: ConfigurableCompiler) = {
    if (enabled) {
      super.compilerModification(compiler)
    }
  }

}
