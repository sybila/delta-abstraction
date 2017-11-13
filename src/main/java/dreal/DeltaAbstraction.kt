package dreal

import kotlinx.coroutines.experimental.async
import kotlinx.coroutines.experimental.newFixedThreadPoolContext
import kotlin.coroutines.experimental.buildSequence

private val POOL = newFixedThreadPoolContext(Runtime.getRuntime().availableProcessors(), "abstraction")

fun ModelFactory.makeStateSpace(partitioning: List<Rectangle>): DeltaModel {

    val stateSpace = buildSequence {
        //TODO: We don't handle exterior states
        yieldAll(partitioning.asSequence().map { State.Interior(it) })
        for (from in partitioning) {
            (partitioning - from)
                    .filter { from.getFacetIntersection(it) != null }
                    .forEach { yield(State.Transition(from, it)) }
        }
    }.toSet()

    val transitionSpace = stateSpace.map { start ->
        start to when (start) {
            is State.Interior -> stateSpace.filter { it == start || (it is State.Transition && it.from == start.rectangle) }
            is State.Transition -> if (start.from == null || start.to == null) emptyList() else {
                stateSpace.filter {
                    (it is State.Interior && it.rectangle == start.to) ||
                    (it is State.Transition && it.from == start.to)
                }
            }
            else -> emptyList()
        }
    }.toMap()

    return DeltaModel(partitioning, this, stateSpace.toList(), transitionSpace)
}

suspend fun DeltaModel.filterAdmissibleStates(tMax: Double): DeltaModel {

    var progess = 0
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

                it.takeIf { !checkNotSat(safetyQuery) }
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

                it.takeIf { !checkNotSat(admissibilityQuery) }
            }
            else -> null
        }
    } }.mapNotNull { it.await().also {
        progess += 1
        if (progess % 10 == 0) println("S: $progess / ${states.size}")
    } }

    println("Unsafe states ${admissibleStates.count { it is State.Interior }}")

    val admissibleTransitions = transitions
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
            transitions = reachableTransitions
    )
}

private inline fun List<String>.makeLines(action: (Int, String) -> String): String = this.mapIndexed(action).joinToString(separator = "\n")

private fun Rectangle.interval(dim: Int): String = "[${bound(dim, false)}, ${bound(dim, true)}]"