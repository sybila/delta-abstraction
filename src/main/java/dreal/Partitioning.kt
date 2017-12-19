package dreal

import com.github.sybila.ode.generator.NodeEncoder
import com.github.sybila.ode.model.OdeModel
import kotlin.coroutines.experimental.buildSequence

data class Partitioning(val items: Set<Item>) {

    data class Item(
            val bounds: Rectangle,
            val provedSafe: Double = Double.NEGATIVE_INFINITY   // negative infinity is a placeholder for "we don't know"
    ) {

        val isSafe: Boolean
            get() = provedSafe >= 0.0

        override fun toString(): String {
            return "PI[safety($provedSafe), $bounds]"
        }
    }

    override fun toString(): String = items.toString()
}

fun OdeModel.granularPartitioning(steps: Int): Partitioning {
    val stepSize = variables
            .map { it.range  }.map { (l, h) -> (h - l) / steps.toDouble() }
            .min()!!

    val thresholds = variables.map {
        val (l, h) = it.range
        buildSequence {
            var t = l
            do {
                yield(t)
                t += stepSize
            } while (t < (h - stepSize/2))
            yield(h)
        }.toList()
    }

    val newModel = OdeModel(variables.mapIndexed { i, v -> v.copy(thresholds = thresholds[i]) })

    val encoder = NodeEncoder(newModel)

    return Partitioning((0 until encoder.stateCount).map { s ->
        val t = encoder.decodeNode(s)
        Partitioning.Item(Rectangle(DoubleArray(2 * t.size) {
            val d = it / 2
            if (it % 2 == 0) thresholds[d][t[d]] else thresholds[d][t[d]+1]
        }))
    }.toSet())
}

suspend fun ModelFactory.refineUnsafe(partitioning: Partitioning): Partitioning {
    val done = partitioning.items.filter { it.isSafe || it.bounds.volume < Config.partitionPrecision }
    val toRefine = partitioning.items - done

    println("Refine partitioning: ${partitioning.items.size} (Unsafe volume: ${toRefine.map { it.bounds.volume }.sum()})")

    val refined = toRefine.flatMap { (r, _) -> r.split() }.mapParallel { r ->
        when {
            maybeHasZero(r) -> Partitioning.Item(r)  // if it has zero, we will never prove safety
            isSafeWithin(r, Config.tMax / 16.0) -> Partitioning.Item(r, Config.tMax / 16.0)
            isSafeWithin(r, Config.tMax / 4.0) -> Partitioning.Item(r, Config.tMax / 4.0)
            isSafeWithin(r, Config.tMax) -> Partitioning.Item(r, Config.tMax)
            else -> Partitioning.Item(r)
        }
    }

    return Partitioning((done + refined).toSet())
}