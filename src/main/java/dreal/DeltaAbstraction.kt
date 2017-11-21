package dreal

import dreal.project.Config
import dreal.project.Partitioning
import dreal.project.TransitionSystem
import kotlinx.coroutines.experimental.async
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicLong
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
            } + State.Exterior
        }).map { index[start]!! to index[it]!! }
    }

    return DeltaModel(partitioning, this, TransitionSystem(stateSpace, edges))
}

suspend fun ModelFactory.checkStates(system: TransitionSystem<State>): TransitionSystem<State> {

    val originalStates = system.states
    val admissibleStates = system.states.filterParallel { state ->
        when (state) {
            is State.Exterior -> true
            is State.Transition -> {
                val (r, dimension, positive) = state.from.getFacetIntersection(state.to) ?: error("Invalid transition state $state")
                val admissibilityQuery =
                """
                ${names.makeLines { i, name -> "(declare-fun $name () Real ${r.interval(i)})" }}
                (assert (${if (positive) "<" else ">" } 0 ${makeModelEquation(dimension)}))
                """
                !provedUnsat(makeQuery(admissibilityQuery))
            }
            is State.Interior -> {
                val r = state.rectangle
                !provedUnsatWithin { tMax ->
                    """
                        ${names.makeLines { i, name -> "(declare-fun $name () Real ${r.interval(i)})" }}
                        ${names.makeLines { i, name -> "(declare-fun ${name}_0_0 () Real ${r.interval(i)})" }}
                        ${names.makeLines { i, name -> "(declare-fun ${name}_0_t () Real ${r.interval(i)})" }}

                        (declare-fun time () Real [0.0, $tMax])

                        (define-ode flow_1 (
                            ${names.makeLines { i, name -> "(= d/dt[$name] ${makeModelEquation(i)})" }}
                        ))

                        (assert (= time $tMax))
                        (assert (= [${names.joinToString(separator = " ") { it + "_0_t" }}] (integral 0. time [${names.joinToString(separator = " ") { it + "_0_0" }}] flow_1)))

                        ; WARNING: dReal is magic and these three asserts, while useless speed up the computation significantly!!
                        (assert (and ${names.makeLines { i, name ->
                            "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
                        }}))
                        (assert (and ${names.makeLines { i, name ->
                            "(<= ${name}_0_0 ${r.bound(i, true)}) (>= ${name}_0_0 ${r.bound(i, false)})"
                        }}))
                        (assert (forall_t 1 [0 time] (and ${names.makeLines { i, name ->
                            "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
                        }})))
                    """
                }
            }
        }
    }
    val admissibleSet = admissibleStates.toSet()

    val inducedTransitions = system.edges.mapNotNull { (from, to) ->
        val start = originalStates[from]
        val end = originalStates[to]
        if (start !in admissibleSet || end !in admissibleSet) null else {
            val newFrom = admissibleStates.indexOf(start)
            val newTo = admissibleStates.indexOf(end)
            newFrom to newTo
        }
    }

    return TransitionSystem(admissibleStates, inducedTransitions)
}

suspend fun ModelFactory.checkTransitions(system: TransitionSystem<State>): TransitionSystem<State> {

    val admissibleTransitions = system.edges.filterParallel { (s, t) ->
        val source = system.states[s]
        val target = system.states[t]
        when (source) {
            is State.Exterior -> {
                if (target is State.Interior) error("Unexpected transition from $source to $target")
                // We don't have any stricter checks from exterior states.
                true
            }
            is State.Interior -> {
                when (target) {
                    is State.Exterior -> error("Unexpected transition from $source to $target")
                    is State.Interior -> if (source == target) true else error("Unexpected transition from $source to $target")
                    is State.Transition -> {
                        // We can check a stricter condition at this point - backwards safety of target.
                        // If target is safe, all trajectories flowing through target originate outside and this edge is unnecessary.
                        /*!provedUnsatWithin { tMax ->
                            val r = source.rectangle
                            val (tR, dimension, positive) = target.from.getFacetIntersection(target.to)!!
                            """
                                ${names.makeLines { i, name -> "(declare-fun $name () Real ${r.interval(i)})" }}
                                ${names.makeLines { i, name -> "(declare-fun ${name}_0_0 () Real ${tR.interval(i)})" }}
                                ${names.makeLines { i, name -> "(declare-fun ${name}_0_t () Real ${r.interval(i)})" }}

                                (declare-fun time () Real [-$tMax, 0.0])

                                (define-ode flow_1 (
                                    ${names.makeLines { i, name -> "(= d/dt[$name] ${makeModelEquation(i)})" }}
                                ))

                                (assert (= time -$tMax))
                                (assert (= [${names.joinToString(separator = " ") { it + "_0_t" }}] (integral 0. time [${names.joinToString(separator = " ") { it + "_0_0" }}] flow_1)))

                                ; Facet flow condition
                                (assert (${if (positive) "<" else ">" } 0 ${makeModelEquation(dimension, names.map { it+"_0_0" })}))

                                ; Facet location condition
                                (assert (and ${names.makeLines { i, name ->
                                        "(<= ${name}_0_0 ${tR.bound(i, true)}) (>= ${name}_0_0 ${tR.bound(i, false)})"
                                    }}))

                                ; Flow conditions
                                (assert (and ${names.makeLines { i, name ->
                                    "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
                                }}))
                                (assert (forall_t 1 [0 time] (and ${names.makeLines { i, name ->
                                    "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
                                }})))
                            """.also { println(it) }
                        }
                        At the moment, this seems to be a bit too much on dReal :/ See for example this result:
                        The trajectories exist, but their origin is so small, the "guaranteed" simulation seems to fail.
                        (set-logic QF_NRA_ODE)

                        (declare-fun x () Real [3.438878, 4.0])
                        (declare-fun y () Real [-0.4, 0.0])
                        (declare-fun x_0_0 () Real [3.438878, 3.438878])
                        (declare-fun y_0_0 () Real [-0.4, 0.0])
                        (declare-fun x_0_t () Real [3.438878, 4.0])
                        (declare-fun y_0_t () Real [-0.4, 0.0])

                        (declare-fun time () Real [-0.2, 0.0])

                        (define-ode flow_1 (
                            (= d/dt[x] (+ (* 1.0 y)))
                        (= d/dt[y] (+ (* 2.0 y) (* -2.0 y (pow x 2.0)) (* -1.0 x)))
                        ))

                        (assert (= time -0.2))
                        (assert (= [x_0_t y_0_t] (integral 0. time [x_0_0 y_0_0] flow_1)))

                        ; Facet flow condition
                        (assert (> 0 (+ (* 1.0 y_0_0))))

                        ; Facet location condition
                        (assert (and (<= x_0_0 3.438878) (>= x_0_0 3.438878)
                        (<= y_0_0 0.0) (>= y_0_0 -0.4)))

                        ; Flow conditions
                        (assert (and (<= x_0_t 4.0) (>= x_0_t 3.438878)
                        (<= y_0_t 0.0) (>= y_0_t -0.4)))
                        (assert (forall_t 1 [0 time] (and (<= x_0_t 4.0) (>= x_0_t 3.438878)
                        (<= y_0_t 0.0) (>= y_0_t -0.4))))

                        (check-sat)
                        (exit)

                        */
                        true
                    }
                }
            }
            is State.Transition -> {
                when (target) {
                    is State.Exterior -> true   // there is not strict check for exiting the system.
                    is State.Interior -> {
                        // We can check a stricter condition at this point - forward safety of source.
                        // If the source is safe, all trajectories flowing through source end outside and this edge is unnecessary.
                        /*!provedUnsatWithin { tMax ->
                            val r = target.rectangle
                            val (sR, dimension, positive) = source.from.getFacetIntersection(source.to)!!
                            """
                                ${names.makeLines { i, name -> "(declare-fun $name () Real ${r.interval(i)})" }}
                                ${names.makeLines { i, name -> "(declare-fun ${name}_0_0 () Real ${sR.interval(i)})" }}
                                ${names.makeLines { i, name -> "(declare-fun ${name}_0_t () Real ${r.interval(i)})" }}

                                (declare-fun time () Real [0.0, $tMax])

                                (define-ode flow_1 (
                                    ${names.makeLines { i, name -> "(= d/dt[$name] ${makeModelEquation(i)})" }}
                                ))

                                (assert (= time $tMax))
                                (assert (= [${names.joinToString(separator = " ") { it + "_0_t" }}] (integral 0. time [${names.joinToString(separator = " ") { it + "_0_0" }}] flow_1)))

                                ; Facet flow condition
                                (assert (${if (positive) "<" else ">" } 0 ${makeModelEquation(dimension, names.map { it+"_0_0" })}))

                                ; Facet location condition
                                (assert (and ${names.makeLines { i, name ->
                                    "(<= ${name}_0_0 ${sR.bound(i, true)}) (>= ${name}_0_0 ${sR.bound(i, false)})"
                                }}))

                                ; Flow conditions
                                (assert (and ${names.makeLines { i, name ->
                                    "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
                                }}))
                                (assert (forall_t 1 [0 time] (and ${names.makeLines { i, name ->
                                    "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
                                }})))
                            """
                        }
                        Also disabled for the moment. See above.
                        */
                        true
                    }
                    is State.Transition -> {
                        val bounds = source.to
                        val (sR, sDim, sPositive) = source.from.getFacetIntersection(source.to)!!
                        val (tR, tDim, tPositive) = target.from.getFacetIntersection(target.to)!!
                        maybeSatWithin { tMax ->
                            """
                                ${names.makeLines { i, name -> "(declare-fun $name () Real ${bounds.interval(i)})" }}
                                ${names.makeLines { i, name -> "(declare-fun ${name}_0_0 () Real ${bounds.interval(i)})" }}
                                ${names.makeLines { i, name -> "(declare-fun ${name}_0_t () Real ${bounds.interval(i)})" }}

                                (declare-fun time () Real [0.0, $tMax])

                                (define-ode flow_1 (
                                    ${names.makeLines { i, name -> "(= d/dt[$name] ${makeModelEquation(i)})" }}
                                ))

                                (assert (= [${names.joinToString(separator = " ") { it + "_0_t" }}] (integral 0. time [${names.joinToString(separator = " ") { it + "_0_0" }}] flow_1)))

                                ; Start facet
                                (assert (and ${names.makeLines { i, name ->
                                    "(<= ${name}_0_0 ${sR.bound(i, true)}) (>= ${name}_0_0 ${sR.bound(i, false)})"
                                }}))
                                (assert (${if (sPositive) "<" else ">" } 0 ${makeModelEquation(sDim, names = names.map { it + "_0_0" })}))

                                ; End facet
                                (assert (and ${names.makeLines { i, name ->
                                    "(<= ${name}_0_t ${tR.bound(i, true)}) (>= ${name}_0_t ${tR.bound(i, false)})"
                                }}))
                                (assert (${if (tPositive) "<" else ">" } 0 ${makeModelEquation(tDim, names = names.map { it + "_0_t" })}))

                                (assert (forall_t 1 [0 time] (and ${names.makeLines { i, name ->
                                    "(<= ${name}_0_t ${bounds.bound(i, true)}) (>= ${name}_0_t ${bounds.bound(i, false)})"
                                }})))
                            """
                        }
                    }
                }
            }
        }
    }

    return TransitionSystem(system.states, admissibleTransitions)
}

private inline fun List<String>.makeLines(action: (Int, String) -> String): String = this.mapIndexed(action).joinToString(separator = "\n")

private fun Rectangle.interval(dim: Int): String = "[${bound(dim, false)}, ${bound(dim, true)}]"

private suspend inline fun <T: Any> List<T>.filterParallel(crossinline action: (T) -> Boolean): List<T> {
    val lastPrint = AtomicLong(0L)
    val progress = AtomicInteger(0)
    return this.map { async(Config.threadPool) {
        it to action(it).also {
            progress.incrementAndGet()
            val last = lastPrint.get()
            val current = System.currentTimeMillis()
            if (current > last + 1000 && lastPrint.compareAndSet(last, current)) {
                println("Progress: ${progress.get()} / ${this@filterParallel.size}")
            }
        }
    } }
            .map { it.await() }
            .mapNotNull { (a, b) -> if (b) a else null }
}

private inline fun provedUnsatWithin(tMax: Double = Config.tMax, queryBuilder: (Double) -> String): Boolean {
    val timeStep = tMax / 10.0
    val times = (0..10).map { it * timeStep }
    return times.any { t -> provedUnsat(makeQuery(queryBuilder(t))) }
}

private inline fun maybeSatWithin(tMax: Double = Config.tMax, queryBuilder: (Double) -> String): Boolean {
    val timeStep = tMax / 5.0
    val times = (0..5).map { it * timeStep }
    return times.any { t -> !provedUnsat(makeQuery(queryBuilder(t))) }
}

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
*/