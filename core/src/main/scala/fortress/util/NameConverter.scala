package fortress.util

/** We add affixes to all variable and function names when converting to SMT-LIB
  * to avoid having reserved keywords as identifiers
  */
object NameConverter {
    // Function to wrap name in |...| for SMTLIB identifiers
    def nameWithQuote(name: String): String = "|" + name + "|"

    // Removes |...| wrapping from a name
    def nameWithoutQuote(name: String): String =
      if (name.startsWith("|") && name.endsWith("|")) name.substring(1, name.length - 1)
      else name

    // Removes all "|" characters from str, useful for when str is a stringification of a term that could contain
    // quoted identifiers
    def removeAllQuotes(str: String): String = str.replace("|", "")
}
