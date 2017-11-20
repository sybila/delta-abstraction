package dreal
import com.github.sybila.ode.model.OdeModel
import dreal.project.Partitioning
import kotlin.coroutines.experimental.buildSequence

inline fun DoubleArray.findInterval(action: (a: Double, b: Double) -> Boolean): Pair<Double, Double>? {
    return (0 until this.size).step(2)
            .firstOrNull { action(this[it], this[it +1]) }
            ?.let { this[it] to this[it +1] }
}

inline fun <reified R> DoubleArray.mapIntervals(action: (a: Double, b: Double) -> R): Array<R> {
    return Array(this.size / 2) { i ->
        action(this[2*i], this[2*i + 1])
    }
}