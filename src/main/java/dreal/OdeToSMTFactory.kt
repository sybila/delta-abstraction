package dreal

import com.github.sybila.ode.model.Evaluable
import com.github.sybila.ode.model.OdeModel
import com.github.sybila.ode.model.Pow

fun OdeModel.toModelFactory() = object : ModelFactory {

    val ode = this@toModelFactory

    override val names: List<String> = ode.variables.map { it.name }

    override fun makeModelEquation(i: Int, names: List<String>): String {
        val eq = ode.variables[i].equation
        val summands = eq.map { s ->
            val m = listOf(s.constant.toString()) + s.variableIndices.map { names[it] } + s.evaluable.map { it.toSMT(names) }
            "(* ${m.joinToString(separator = " ")})"
        }
        return "(+ ${summands.joinToString(separator = " ")})"
    }

    override fun dimensionBounds(i: Int): Pair<Double, Double> = ode.variables[i].range

}

fun Evaluable.toSMT(names: List<String>): String = when (this) {
    is Pow -> "(pow ${names[this.varIndex]} ${this.degree})"
    else -> error("unsupported evaluable $this")
}