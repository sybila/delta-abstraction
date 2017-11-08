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
(declare-fun x () Real [${r.bound(0, false)}, ${r.bound(0, true)}])
(declare-fun y () Real [${r.bound(1, false)}, ${r.bound(1, true)}])

(declare-fun x_0_0 () Real [${r.bound(0, false)}, ${r.bound(0, true)}])
(declare-fun y_0_0 () Real [${r.bound(1, false)}, ${r.bound(1, true)}])

(declare-fun x_0_t () Real [${r.bound(0, false)}, ${r.bound(0, true)}])
(declare-fun y_0_t () Real [${r.bound(1, false)}, ${r.bound(1, true)}])

(declare-fun time () Real [0.0, $tMax])

(define-ode flow_1 (
    (= d/dt[x] ${makeModelEquation(0, names = listOf("x", "y"))})
    (= d/dt[y] ${makeModelEquation(1, names = listOf("x", "y"))})
))

(assert (= time $tMax))
(assert (= [x_0_t y_0_t] (integral 0. time [x_0_0 y_0_0] flow_1)))
; WARNING: dReal is magic and these three asserts, while useless speed up the computation significantly!!
(assert (and
    (<= x_0_t ${r.bound(0, true)}) (>= x_0_t ${r.bound(0, false)})
    (<= y_0_t ${r.bound(1, true)}) (>= y_0_t ${r.bound(1, false)})
))
(assert (and
    (<= x_0_0 ${r.bound(0, true)}) (>= x_0_0 ${r.bound(0, false)})
    (<= y_0_0 ${r.bound(1, true)}) (>= y_0_0 ${r.bound(1, false)})
))
(assert (forall_t 1 [0 time] (and
    (<= x_0_t ${r.bound(0, true)}) (>= x_0_t ${r.bound(0, false)})
    (<= y_0_t ${r.bound(1, true)}) (>= y_0_t ${r.bound(1, false)})
)))
""")
                it.takeIf { !checkNotSat(safetyQuery) }
            }
            is State.Transition -> if (it.from == null || it.to == null) null else {
                val (r, dimension, positive) = it.from.getFacetIntersection(it.to)!!
                val admissibilityQuery = makeQuery(
"""
(declare-fun x () Real [${r.bound(0, false)}, ${r.bound(0, true)}])
(declare-fun y () Real [${r.bound(1, false)}, ${r.bound(1, true)}])
(assert (${if (positive) "<" else ">" } 0 ${makeModelEquation(dimension, names = listOf("x", "y"))}))
""")

                it.takeIf { !checkNotSat(admissibilityQuery) }
            }
            else -> null
        }
    } }.mapNotNull { it.await().also {
        progess += 1
        if (progess % 10 == 0) println("S: $progess / ${states.size}")
    } }

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
(declare-fun x () Real [${bounds.bound(0, false)}, ${bounds.bound(0, true)}])
(declare-fun y () Real [${bounds.bound(1, false)}, ${bounds.bound(1, true)}])

(declare-fun x_0_0 () Real [${bounds.bound(0, false)}, ${bounds.bound(0, true)}])
(declare-fun y_0_0 () Real [${bounds.bound(1, false)}, ${bounds.bound(1, true)}])

(declare-fun x_0_t () Real [${bounds.bound(0, false)}, ${bounds.bound(0, true)}])
(declare-fun y_0_t () Real [${bounds.bound(1, false)}, ${bounds.bound(1, true)}])

(declare-fun time () Real [0.0, $tMax])

(define-ode flow_1 (
    (= d/dt[x] ${makeModelEquation(0, names = listOf("x", "y"))})
    (= d/dt[y] ${makeModelEquation(1, names = listOf("x", "y"))})
))

(assert (= [x_0_t y_0_t] (integral 0. time [x_0_0 y_0_0] flow_1)))

; Start facet
(assert (and
    (<= x_0_0 ${start.bound(0, true)}) (>= x_0_0 ${start.bound(0, false)})
    (<= y_0_0 ${start.bound(1, true)}) (>= y_0_0 ${start.bound(1, false)})
))
(assert (${if (sPositive) "<" else ">" } 0 ${makeModelEquation(sDim, names = listOf("x_0_0", "y_0_0"))}))

; End facet
(assert (and
    (<= x_0_t ${target.bound(0, true)}) (>= x_0_t ${target.bound(0, false)})
    (<= y_0_t ${target.bound(1, true)}) (>= y_0_t ${target.bound(1, false)})
))
(assert (${if (tPositive) "<" else ">" } 0 ${makeModelEquation(tDim, names = listOf("x_0_t", "y_0_t"))}))

(assert (> time 0.001))

; WARNING: dReal is magic and these three asserts, while useless speed up the computation significantly!!
(assert (forall_t 1 [0 time] (and
    (<= x_0_t ${bounds.bound(0, true)}) (>= x_0_t ${bounds.bound(0, false)})
    (<= y_0_t ${bounds.bound(1, true)}) (>= y_0_t ${bounds.bound(1, false)})
)))
""")

                    if (from.from.bound(1, false) == -4.0 && from.from == to.to) {
                        println(reachQuery)
                    }
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