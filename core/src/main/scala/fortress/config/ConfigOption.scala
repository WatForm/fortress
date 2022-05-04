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
class ConfigOption(optionName: String, action: (ConfigurableCompiler => Unit) = (_ => ())) {

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

trait Toggleable extends ConfigOption {
  protected var enabled: Boolean = true

  def isEnabled() = enabled

  def enable() = {
    enabled = true
  }

  def disable() = {
    enabled = false
  }

  def toggle = {
    enabled = !enabled
  }

  override def modifyCompiler(compiler: ConfigurableCompiler): Unit = {
    if (enabled) {
      compilerModification(compiler)
    }
  }
}

/**
  * An option which will only activate while it is enabled
  *
  * @param name
  * @param defaultValue true if the option should start enabled
  */
class ToggleOption(optionName: String, action: ConfigurableCompiler => Unit = (_ => ()), defaultState: Boolean = true) extends ConfigOption(optionName, action) with Toggleable {
  // Override enabled to default value
  enabled = defaultState
}

/**
  * A collection of prioritized options which can be controlled individually.
  *
  * @param optionName
  */
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

    def getOptions(): Seq[ConfigOption] = getOptionsByPriority()

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

/**
  * A Group of prioritized options, which can be collectively enabled or disabled
  *
  * @param optionName
  * @param defaultState
  */
class ToggleGroupOption(optionName: String, defaultState: Boolean = true) extends GroupOption(optionName) with Toggleable {
  // Override initial enabled state with default value
  enabled = defaultState
}

