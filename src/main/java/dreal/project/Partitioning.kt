package dreal.project

import com.github.sybila.ode.generator.NodeEncoder
import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.OdeModel
import dreal.Rectangle

data class Partitioning(val items: List<Item>) {

    data class Item(
            val bounds: Rectangle,
            val maxTime: Double = 0.0,
            val isSafe: Boolean? = null
    )
}

fun OdeModel.exportPartitioning(): Partitioning {

    val encoder = NodeEncoder(this)
    val ts = RectangleOdeModel(this, true)

    val items = (0 until ts.stateCount).map { s ->
        val rectangle = Rectangle(variables.indices.flatMap { i ->
            val t = variables[i].thresholds
            listOf(t[encoder.lowerThreshold(s, i)], t[encoder.upperThreshold(s, i)])
        }.toDoubleArray())

        ts.run {
            if (s.successors(true).asSequence().all { it.target != s }) {
                // There is no self-loop, therefore the state is safe!
                // Partitioning.Item(rectangle, Double.POSITIVE_INFINITY, true)
                // But that only holds if we use the piece-wise multi affine system afterwards, which is generally not true :/
                Partitioning.Item(rectangle)
            } else {
                // There is a self-loop, the state is potentially unsafe.
                Partitioning.Item(rectangle)
            }
        }
    }

    return Partitioning(items)
}