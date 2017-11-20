package dreal

import dreal.project.Partitioning
import dreal.project.TransitionSystem
import kotlin.coroutines.experimental.buildSequence

fun ModelFactory.makeStateSpace(partitioning: Partitioning): DeltaModel {

    val rectangles = partitioning.items.map { it.bounds }
    val stateSpace = buildSequence {
        yield(State.Exterior)

        for ((r, _, safe) in partitioning.items) {
            if (safe != true) {
                yield(State.Interior(r))
            }
        }

        for (from in rectangles) {
            for (to in rectangles) {
                if (from != to && from.getFacetIntersection(to) != null) {
                    yield(State.Transition(from, to))
                }
            }
            boundsRect.facets.forEach { facet ->
                if (from.getFacetIntersection(facet) != null) {
                    yield(State.Transition(from, facet))
                    yield(State.Transition(facet, from))
                }
            }
        }
    }.toList()

    val index = stateSpace.mapIndexed { i, s -> s to i }.toMap()

    val edges = stateSpace.flatMap { start ->
        (when (start) {
            is State.Interior -> stateSpace.filter { it == start || (it is State.Transition && it.from == start.rectangle) }
            is State.Transition -> stateSpace.filter {
                (it is State.Interior && it.rectangle == start.to) ||
                (it is State.Transition && start.to.degenrateDimensions == 0 && it.from == start.to) ||
                (it is State.Exterior && start.to.degenrateDimensions > 0)
            }
            is State.Exterior -> stateSpace.filter {
                it is State.Transition && it.from.degenrateDimensions > 0
            }
        }).map { index[start]!! to index[it]!! }
    }

    return DeltaModel(partitioning, this, TransitionSystem(stateSpace, edges))
}
/*
fun ModelFactory.checkAdmissible(system: TransitionSystem<State>): TransitionSystem<State> {



}*/

/*
suspend fun OdeModel.makePartitioning(tMax: Double, precision: Double): Partitioning {

    val safe = HashSet<Rectangle>()
    val unsafe = HashSet<Rectangle>()
    var process = listOf(Rectangle(DoubleArray(variables.size * 2) { i ->
        val dim = i / 2
        if (i % 2 == 0) variables[dim].range.first else variables[dim].range.second
    }))

    this.toModelFactory().run {
        while (process.isNotEmpty()) {
            val next = ArrayList<Rectangle>()
            process.map { r -> async(POOL) {
                val safetyQuery = makeQuery(
                        """
${names.makeLines { i, name ->
                            "(declare-fun $name () Real ${r.interval(i)})"
                        }}

${names.makeLines { i, name ->
                            "(declare-fun ${name}_0_0 () Real ${r.interval(i)})"
                        }}

${names.makeLines { i, name ->
                            "(declare-fun ${name}_0_t () Real ${r.interval(i)})"
                        }}

(declare-fun time () Real [0.0, $tMax])

(define-ode flow_1 (
${names.makeLines { i, name ->
                            "(= d/dt[$name] ${makeModelEquation(i)})"
                        }}
))

(assert (= time $tMax))
(assert (= [${names.joinToString(separator = " ") { it + "_0_t" }}] (integral 0. time [${names.joinToString(separator = " ") { it + "_0_0" }}] flow_1)))

; WARNING: dReal is magic and these three asserts, while useless speed up the computation significantly!!
(assert (and
${names.makeLines { i, name ->
                            "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
                        }}
))
(assert (and
${names.makeLines { i, name ->
                            "(<= ${name}_0_0 ${r.bound(i, true)}) (>= ${name}_0_0 ${r.bound(i, false)})"
                        }}
))
(assert (forall_t 1 [0 time] (and
${names.makeLines { i, name ->
                            "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
                        }}
)))
""")
                if (checkNotSat(safetyQuery)) {
                    synchronized(safe) { safe.add(r) }
                } else {
                    val avr = (0 until r.dimensions).map { d -> r.vertices.map { eval(d, it) }.average() }
                    /*var max = 0 to 1
                    for (i in avr.indices) {
                        for (j in avr.indices) {
                            if (i != j) {
                                val dRatio = avr[i] / avr[j]
                                val rRation = r.size(i) / r.size(j)
                            }
                        }
                    }
                    val maxDim = (0 until r.dimensions).minBy { d ->
                        r.vertices.map { eval(d, it) }.average()
                    }!!*/
                    //val maxDim = if (avr[0] / avr[1] > r.size(0) / r.size(1)) 0 else 1
                    val maxDim = (0 until r.dimensions).maxBy { r.bound(it, true) - r.bound(it, false) }!!
                    if (r.bound(maxDim, true) - r.bound(maxDim, false) > precision) {
                        val (l, h) = r.split(maxDim)
                        synchronized(next) {
                            next.add(l)
                            next.add(h)
                        }
                    } else {
                        synchronized(unsafe) {
                            unsafe.add(r)
                        }
                    }
                }
            } }.map { it.await() }
            println("Process: ${process.size}")
            process = next
        }
    }


    return Partitioning(safe.map { it to true } + unsafe.map { it to false })

}

suspend fun DeltaModel.filterAdmissibleStates(tMax: Double): DeltaModel {

    var progess = 0
    val admissible = AtomicInteger(0)
    val total = AtomicInteger(0)
    val admissibleStates = states.map { async(POOL) {
        when (it) {
            is State.Interior -> {
                val r = it.rectangle
                val safetyQuery = makeQuery(
"""
${names.makeLines { i, name ->
    "(declare-fun $name () Real ${r.interval(i)})"
}}

${names.makeLines { i, name ->
    "(declare-fun ${name}_0_0 () Real ${r.interval(i)})"
}}

${names.makeLines { i, name ->
    "(declare-fun ${name}_0_t () Real ${r.interval(i)})"
}}

(declare-fun time () Real [0.0, $tMax])

(define-ode flow_1 (
    ${names.makeLines { i, name ->
    "(= d/dt[$name] ${makeModelEquation(i)})"
}}
))

(assert (= time $tMax))
(assert (= [${names.joinToString(separator = " ") { it + "_0_t" }}] (integral 0. time [${names.joinToString(separator = " ") { it + "_0_0" }}] flow_1)))

; WARNING: dReal is magic and these three asserts, while useless speed up the computation significantly!!
(assert (and
    ${names.makeLines { i, name ->
        "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
    }}
))
(assert (and
    ${names.makeLines { i, name ->
        "(<= ${name}_0_0 ${r.bound(i, true)}) (>= ${name}_0_0 ${r.bound(i, false)})"
    }}
))
(assert (forall_t 1 [0 time] (and
    ${names.makeLines { i, name ->
        "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
    }}
)))
""")

                //println(safetyQuery)

                it.takeIf { !(partitioning.rectangles.find { it.first == r }?.second ?: checkNotSat(safetyQuery).also {
                    if (it) admissible.incrementAndGet()
                    if (total.incrementAndGet() % 100 == 0) {
                        println("${admissible.get()} / ${total.get()} / ${states.size}")
                    }
                }) }
            }
            is State.Transition -> if (it.from == null || it.to == null) null else {
                val (r, dimension, positive) = it.from.getFacetIntersection(it.to)!!
                val admissibilityQuery = makeQuery(
"""
${names.makeLines { i, name ->
    "(declare-fun $name () Real ${r.interval(i)})"
}}
(assert (${if (positive) "<" else ">" } 0 ${makeModelEquation(dimension)}))
""")

                it.takeIf { !checkNotSat(admissibilityQuery).also {
                    if (it) admissible.incrementAndGet()
                    if (total.incrementAndGet() % 100 == 0) {
                        println("${admissible.get()} / ${total.get()} / ${states.size}")
                    }
                } }
            }
            else -> null
        }
    } }.mapNotNull { it.await()/*.also {
        progess += 1
        if (progess % 10 == 0) println("S: $progess / ${states.size}")
    }*/ }

    println("Unsafe states ${admissibleStates.count { it is State.Interior }}")

    val admissibleTransitions = system
            .filterKeys { it in admissibleStates }
            .mapValues { entry -> entry.value.filter { it in admissibleStates } }


    var tProgress = 0
    var tCount = 0
    val reachableTransitions = admissibleTransitions
            .flatMap { e -> e.value.map { (e.key to it).also { tCount += 1 } } }
            .map { (from, to) -> async(POOL) {
                if (from is State.Transition && to is State.Transition && from.to != null && from.from != null && to.to != null && to.from != null) {
                    val bounds = from.to
                    val (start, sDim, sPositive) = from.from.getFacetIntersection(from.to)!!
                    val (target, tDim, tPositive) = to.from.getFacetIntersection(to.to)!!
                    val reachQuery = makeQuery(
                            """
${names.makeLines { i, name ->
    "(declare-fun $name () Real ${bounds.interval(i)})"
}}

${names.makeLines { i, name ->
    "(declare-fun ${name}_0_0 () Real ${bounds.interval(i)})"
}}

${names.makeLines { i, name ->
    "(declare-fun ${name}_0_t () Real ${bounds.interval(i)})"
}}

(declare-fun time () Real [0.0, $tMax])

(define-ode flow_1 (
    ${names.makeLines { i, name ->
        "(= d/dt[$name] ${makeModelEquation(i)})"
    }}
))

(assert (= [${names.joinToString(separator = " ") { it + "_0_t" }}] (integral 0. time [${names.joinToString(separator = " ") { it + "_0_0" }}] flow_1)))

; Start facet
(assert (and
    ${names.makeLines { i, name ->
        "(<= ${name}_0_0 ${start.bound(i, true)}) (>= ${name}_0_0 ${start.bound(i, false)})"
    }}
))
(assert (${if (sPositive) "<" else ">" } 0 ${makeModelEquation(sDim, names = names.map { it + "_0_0" })}))

; End facet
(assert (and
    ${names.makeLines { i, name ->
        "(<= ${name}_0_t ${target.bound(i, true)}) (>= ${name}_0_t ${target.bound(i, false)})"
    }}
))
(assert (${if (tPositive) "<" else ">" } 0 ${makeModelEquation(tDim, names = names.map { it + "_0_t" })}))

; WARNING: dReal is magic and these three asserts, while useless speed up the computation significantly!!
(assert (forall_t 1 [0 time] (and
    ${names.makeLines { i, name ->
        "(<= ${name}_0_t ${bounds.bound(i, true)}) (>= ${name}_0_t ${bounds.bound(i, false)})"
    }}
)))
""")

                    /*if (from.from.bound(1, false) == -4.0 && from.from == to.to) {
                        println(reachQuery)
                    }*/
                    //println(reachQuery)

                    (from to to).takeIf { !checkNotSat(reachQuery) }
                } else (from to to)
            } }.mapNotNull { it.await().also {
        tProgress += 1
        if (tProgress % 10 == 0) println("T: $tProgress / $tCount")
    } }.groupBy({ it.first }, { it.second })

    return this.copy(
            states = admissibleStates,
            system = reachableTransitions
    )
}

private inline fun List<String>.makeLines(action: (Int, String) -> String): String = this.mapIndexed(action).joinToString(separator = "\n")

private fun Rectangle.interval(dim: Int): String = "[${bound(dim, false)}, ${bound(dim, true)}]"

*/