package fortress.config

import fortress.compiler.ConfigurableCompiler

abstract class ConfigOption(optionName: String) {

  val name = optionName
  /**
    * Function to modify a configurable compiler based on the option
    *
    * @param compiler
    */
  def modifyCompiler(compiler: ConfigurableCompiler): Unit

}

/**
  * An option which will only activate while it is enabled
  *
  * @param name
  * @param defaultValue true if the option should start enabled
  */
abstract class ToggleOption(optionName: String, defaultValue: Boolean) extends ConfigOption(optionName) {
  protected var enabled: Boolean = defaultValue

  def isEnabled() = enabled

  def enable() = {
    enabled = true
  }

  def disable() = {

  }


  def compilerModification(compiler: ConfigurableCompiler): Unit




}
