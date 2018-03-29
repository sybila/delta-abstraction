package dreal

import com.github.daemontus.Formula
import com.github.daemontus.OdeModel
import com.github.sybila.ode.generator.NodeEncoder
import kotlin.coroutines.experimental.buildSequence

fun OdeModel.toModelFactory() = object : ModelFactory {

    override val dimensions: Int = variables.size

    override val boundsRect: Rectangle = Rectangle(DoubleArray(dimensions * 2) { i ->
        val dim = i / 2
        if (i % 2 == 0) variables[dim].bounds.first else variables[dim].bounds.second
    })

    override val names: List<String> = variables.map { it.name }

    override fun makeModelEquation(i: Int, names: List<String>): String = variables[i].flow.toSMT2(names)

    override fun evalModelEquation(i: Int, values: DoubleArray): Double = variables[i].flow.eval(values)

    private fun Formula.toSMT2(renaming: List<String>): String {
        return when (this) {
            is Formula.Number -> this.value.toString()
            is Formula.Text -> "(\"${this.value}\")"
            is Formula.Function -> {
                if (this.name in names) {
                    // variable
                    renaming[names.indexOf(name)]
                } else {
                    if (this.name == "-" && this.args.size > 1) {
                        // dReal's interpretation of minuses is completely fucked-up...
                        "(+ ${args[0].toSMT2(renaming)} ${args.drop(1).joinToString(separator = " ") { "(- ${it.toSMT2(renaming)})" }})"
                    } else {
                        "($name ${args.joinToString(separator = " ") { it.toSMT2(renaming) }})"
                    }
                    //"($name ${args.joinToString(separator = " ") { it.toSMT2(renaming) }})"
                }
            }
        }
    }

    private fun Formula.eval(values: DoubleArray): Double {
        return when (this) {
            is Formula.Number -> this.value
            is Formula.Text -> error("Text is not allowed")
            is Formula.Function -> {
                val args = this.args.map { it.eval(values) }
                when (this.name) {
                    "+" -> args.fold(0.0) { a, b -> a + b }
                    "*" -> args.fold(1.0) { a, b -> a * b }
                    "-" -> {
                        if (args.size == 1) {
                            -1 * args[0]
                        } else {
                            args.drop(1).fold(args[0]) { a, b -> a - b }
                        }
                    }
                    "/" -> {
                        if (args.size == 1) {
                            1 / args[0]
                        } else {
                            args.drop(1).fold(args[0]) { a, b -> a / b }
                        }
                    }
                    "pow" -> Math.pow(args[0], args[1])
                    "sin" -> Math.sin(args[0])
                    in names -> values[names.indexOf(this.name)]
                    else -> error("Unsupported function ${this.name}")
                }
            }
        }
    }

    override fun dimensionBounds(i: Int): Pair<Double, Double> = variables[i].bounds

    override fun eval(i: Int, at: DoubleArray): Double = evalModelEquation(i, at)
}

fun OdeModel.granularPartitioning(steps: Int): Partitioning {
    val stepSize = variables
            .map { it.bounds }.map { (l, h) -> (h - l) / steps.toDouble() }
            .min()!!

    val thresholds = variables.map {
        val (l, h) = it.bounds
        buildSequence {
            var t = l
            do {
                yield(t)
                t += stepSize
            } while (t < (h - stepSize/2))
            yield(h)
        }.toList()
    }

    val newModel = com.github.sybila.ode.model.OdeModel(thresholds.mapIndexed { i, thres ->
        com.github.sybila.ode.model.OdeModel.Variable(variables[i].name, variables[i].bounds, thres, null, emptyList())
    })

    val encoder = NodeEncoder(newModel)

    return Partitioning((0 until encoder.stateCount).map { s ->
        val t = encoder.decodeNode(s)
        Partitioning.Item(Rectangle(DoubleArray(2 * t.size) {
            val d = it / 2
            if (it % 2 == 0) thresholds[d][t[d]] else thresholds[d][t[d]+1]
        }))
    }.toSet())
}