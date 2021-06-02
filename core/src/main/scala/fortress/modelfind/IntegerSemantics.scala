package fortress.modelfind


/** The semantics to be used for integers during model finding. */
sealed trait IntegerSemantics

/** Treat integers as unbounded integers.
  * These are the traditional semantics for integers, though model finding may not be decidable. 
  */
case object Unbounded extends IntegerSemantics

/** Treat integers using signed modular arithmetic, wrapping around once overflowing.
  * Model finding is decidable, but the differing semantics may affect the question of satisfiability.
  */ 
case class ModularSigned(bitwidth: Int) extends IntegerSemantics

object IntegerSemantics {
    val UnboundedSemantics: IntegerSemantics = Unbounded
    def ModularSignedSemantics(bitwidth: Int): IntegerSemantics = ModularSigned(bitwidth)
}
