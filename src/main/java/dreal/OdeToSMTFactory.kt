package dreal

import com.github.sybila.ode.model.*

fun OdeModel.toModelFactory() = object : ModelFactory {

    val ode = this@toModelFactory

    override val dimensions: Int = ode.variables.size

    override val names: List<String> = ode.variables.map { it.name }

    override val boundsRect: Rectangle = Rectangle(DoubleArray(variables.size * 2) { i ->
        val dim = i / 2
        if (i % 2 == 0) variables[dim].range.first else variables[dim].range.second
    })

    override fun makeModelEquation(i: Int, names: List<String>): String {
        val eq = ode.variables[i].equation
        val summands = eq.map { s ->
            val m = listOf(s.constant.toString()) + s.variableIndices.map { names[it] } + s.evaluable.map { it.toSMT(names) }
            "(* ${m.joinToString(separator = " ")})"
        }
        return "(+ ${summands.joinToString(separator = " ")})"
    }

    override fun dimensionBounds(i: Int): Pair<Double, Double> = ode.variables[i].range

    override fun eval(i: Int, at: DoubleArray): Double {
        val eq = ode.variables[i].equation
        return eq.fold(0.0) { r, s ->
            r + (listOf(s.constant) + s.variableIndices.map { at[it] } + s.evaluable.map { it.eval(at[it.varIndex]) }).fold(1.0) { a, b -> a * b }
        }
    }

}

fun Evaluable.toSMT(names: List<String>): String = when (this) {
    is Pow -> "(pow ${names[this.varIndex]} ${this.degree})"
    is RampApproximation -> {
        when {
            this == RampApproximation(0, doubleArrayOf(-5.0, -1.0, 5.0), doubleArrayOf(4.0, 0.0, 6.0)) -> "(abs (+ x 1))"
            this == RampApproximation(0, doubleArrayOf(-5.0, 1.0, 5.0), doubleArrayOf(6.0, 0.0, 4.0)) -> "(abs (- x 1))"
            else -> error("unsupported evaluable $this")
        }
    }
    is Hill -> "(+ $a (/ (- $b $a) (+ 1 (pow (/ $theta ${names[varIndex]}) $n))))"   //a + (b - a) * (1 / (1 + Math.pow(theta/value, n)))
    else -> error("unsupported evaluable $this")
}