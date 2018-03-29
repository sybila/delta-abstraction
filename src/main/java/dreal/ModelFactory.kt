package dreal

/**
 * A model with two dimensions and one parameter
 */
interface ModelFactory {

    val dimensions: Int
    val boundsRect: Rectangle

    val names: List<String>

    val x: String
        get() = names[0]

    val y: String
        get() = names[1]

    fun makeModelEquation(i: Int, names: List<String> = this.names): String

    fun evalModelEquation(i: Int, values: DoubleArray): Double

    fun dimensionBounds(i: Int): Pair<Double, Double>

    fun unknownDimension(i: Int): Nothing = error("svg.Dimension $i does not exist in $this")

    fun eval(i: Int, at: DoubleArray): Double
}