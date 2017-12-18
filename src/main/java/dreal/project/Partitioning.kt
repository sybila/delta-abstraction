package dreal.project

import com.github.sybila.ode.generator.NodeEncoder
import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.OdeModel
import dreal.Rectangle
import java.util.*
import kotlin.coroutines.experimental.buildSequence

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

class PartitionBuilder(
        model: OdeModel, private val precision: Double
) {

    val stepSize = model.variables.map { it.range.second - it.range.first }.max()!! / precision

    private val thresholds: List<DoubleArray> = model.variables.map {
        val (L, H) = it.range
        buildSequence {
            var t = L
            do {
                yield(t)
                t += stepSize
            } while (t < (H - 0.5 * stepSize))
            yield(H)
        }.toList().toDoubleArray()
    }

    private val rectangles = HashSet<Rectangle>()

    fun closestThreshold(dim: Int, value: Double): Double {
        val t = thresholds[dim]
        val index = t.binarySearch(value)
        return if (index >= 0) value else {    // value is an exact thresholds
            val insertAt = -1 * (index + 1)
            if (insertAt == 0) t[insertAt] else
            if (insertAt == t.size) t[insertAt-1] else {
                val distLower = Math.abs(t[insertAt-1] - value)
                val distHigher = Math.abs(t[insertAt] - value)
                if (distLower < distHigher) t[insertAt-1] else t[insertAt]
            }
        }
    }

    fun normalize(rectangle: Rectangle): Rectangle {
        return Rectangle(DoubleArray(2 * thresholds.size) {
            val dim = it / 2
            if (it % 2 == 0) closestThreshold(dim, rectangle.bound(dim, false))
            else closestThreshold(dim, rectangle.bound(dim, true))
        })
    }

    /**
     * Return true if rectangle was added. (Note that this does not perform any intersection checks)
     */
    fun addRectangle(rectangle: Rectangle): Rectangle? {
        val normalized = normalize(rectangle)
        return when {
            normalized.degenrateDimensions != 0 -> null
            normalized in rectangles -> null
            else -> {
                rectangles.add(normalized)
                normalized
            }
        }
    }

    fun build(): Partitioning {
        // check for rectangle intersections
        val hasIntersection = rectangles.asSequence().flatMap { rectangles.asSequence().map {
            if (it != it) it to it else null
        } }.filterNotNull().find { (a, b) -> a.intersect(b) != null }
        if (hasIntersection != null) error("Invalid partitioning on $hasIntersection")

        return Partitioning(rectangles.map {
            Partitioning.Item(it)
        })
    }

}
/*
fun main(args: Array<String>) {
    // Test PartitionBuilder

    val test = OdeModel(variables = listOf(
            OdeModel.Variable(name = "x", range = -10.0 to 10.0, thresholds = listOf(-10.0, 10.0), varPoints = 1500 to 20)
    ))

    val builder = PartitionBuilder(test)

    println(builder.closestThreshold(0, -11.0))
    println(builder.closestThreshold(0, -9.5))
    println(builder.closestThreshold(0, -2.1))
    println(builder.closestThreshold(0, 0.0))
    println(builder.closestThreshold(0, 5.4))
    println(builder.closestThreshold(0, 22.0))

    println(builder.addRectangle(Rectangle(doubleArrayOf(0.1, 1.4))))
    println(builder.addRectangle(Rectangle(doubleArrayOf(1.4, 1.8))))
    println(builder.addRectangle(Rectangle(doubleArrayOf(1.8, 1.9))))
    println(builder.addRectangle(Rectangle(doubleArrayOf(3.5, 22.4))))

    println(builder.build())

}*/