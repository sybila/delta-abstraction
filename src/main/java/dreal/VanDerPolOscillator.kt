package dreal

/**
 * Model of Van der Pol oscillator with one parameter `p`.
 *
 * For negative parameter values, the limit cycle collapses into a spiral.
 */
/*object VanDerPolOscillator : ModelFactory {

    override val names: List<String> = listOf("x", "y", "p")

    override fun makeModelEquation(i: Int, names: List<String>): String = when (i) {
        0 -> names[1]
        1 -> "(- (* ${names[1]} 2.0 (- 1 (* ${names[0]} ${names[0]}))) ${names[0]})"
        2 -> "0"
        else -> unknownDimension(i)
    }

    override fun dimensionBounds(i: Int): Pair<Double, Double> = when (i) {
        0 -> -10.0 to 10.0
        1 -> -10.0 to 10.0
        2 -> 0.1 to 0.6
        else -> unknownDimension(i)
    }

    override fun eval(i: Int, at: DoubleArray): Double {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }
}*/