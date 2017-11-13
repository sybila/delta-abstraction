package dreal
import com.github.sybila.ode.model.OdeModel
import kotlin.coroutines.experimental.buildSequence


data class Partitioning(
        val rectangles: List<Pair<Rectangle, Boolean?>>
)

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

fun OdeModel.exportPartitioning(): Partitioning {

    fun expandVariable(iVar: Int, rect: List<Double>): Sequence<Rectangle>  = buildSequence {
        val t = variables[iVar].thresholds
        t.dropLast(1).indices
                .map { rect + listOf(t[it], t[it +1]) }
                .forEach {
                    if (iVar + 1 == variables.size) {
                        yield(Rectangle(it.toDoubleArray()))
                    } else {
                        yieldAll(expandVariable(iVar + 1, it))
                    }
                }
    }

    return Partitioning(expandVariable(0, emptyList()).map { it to null }.toList())
}