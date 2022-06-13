package fortress.util

/** We add affixes to all variable and function names when converting to SMT-LIB
  * to avoid having reserved keywords as identifiers
  */
object NameConverter {
    // Function to add affixes to name
    def nameWithAffix(name: String): String = name + "aa"

    // Function to remove affixes from name
    def nameWithoutAffix(name: String): String =
        if (name.endsWith("aa")) name.substring(0, name.length - 2)
        else name
    
    def nameToPython(name: String): String = name.replaceAll("@", "") + "_"
}
