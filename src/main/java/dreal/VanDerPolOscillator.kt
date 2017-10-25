package dreal

/**
 * Model of Van der Pol oscillator with one parameter `p`.
 *
 * For negative parameter values, the limit cycle collapses into a spiral.
 */
object VanDerPolOscillator : ModelFactory {

    override val names: List<String> = listOf("x", "y", "p")

    override fun makeModelEquation(i: Int, names: List<String>): String = when (i) {
        0 -> y
        1 -> "(- (* $y 0.1 (- 1 (* $x $x))) $x)"
        2 -> "0"
        else -> unknownDimension(i)
    }

    override fun dimensionBounds(i: Int): Pair<Double, Double> = when (i) {
        0 -> -20.0 to 20.0
        1 -> -20.0 to 20.0
        2 -> 0.1 to 0.6
        else -> unknownDimension(i)
    }

}