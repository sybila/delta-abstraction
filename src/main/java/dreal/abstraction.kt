package dreal

import com.github.sybila.ode.generator.NodeEncoder
import com.github.sybila.ode.model.OdeModel
import kotlinx.coroutines.experimental.async
import kotlinx.coroutines.experimental.runBlocking
import kotlin.coroutines.experimental.buildSequence

fun main(args: Array<String>) {
    runBlocking {
        G1Sswitch.makePartitions()
    }
}

val FIND = 74

suspend fun OdeModel.makeDeltaAbstraction(modelFactory: ModelFactory): DeltaModel {

    val encoder = NodeEncoder(this)

    val tX = this.variables[0].thresholds
    val tY = this.variables[1].thresholds

    val states = buildSequence {
        // exterior state
        yield(State.Exterior)
        // interior states
        for (s in 0 until encoder.stateCount) {
            yield(State.Interior(s))
        }
        // transition states
        (0 until encoder.stateCount)
                .asSequence()
                .map { s ->
                    buildSequence {
                        yield(encoder.higherNode(s, 0))
                        yield(encoder.higherNode(s, 1))
                        yield(encoder.lowerNode(s, 0))
                        yield(encoder.lowerNode(s, 1))
                    }.toSet().flatMap {
                        listOf(State.Transition(s, it), State.Transition(it, s))    // we add both to include null -> s transitions
                    }
                }
                .forEach { yieldAll(it) }

    }.toSet().toList()

    val enteringSystem: List<Pair<State, List<State>>> = listOf(State.Exterior to states.filter { it is State.Transition && it.from == null })

    val exitingInterior: List<Pair<State, List<State>>> = states.filter { it is State.Interior }.map { s ->
        (s as State.Interior)   // ugly!
        s to states.filter { it is State.Transition && it.from == s.rectangle }
    }

    val exitingEdge: List<Pair<State, List<State>>> = states.filter { it is State.Transition }.map { s ->
        (s as State.Transition) // ugly!
        if (s.to != null) { // interior transitions
            s to states.filter {
                (it is State.Transition && s.to == it.from && true)
                        || (it is State.Interior && it.rectangle == s.to)
            }
        } else {    // going out of the system
            s to listOf(State.Exterior)
        }
    }

    val transitions = (enteringSystem + exitingInterior + exitingEdge).toMap()

    val timeBound = 100

    // check state admissibility
    val admissibleStates = states.map { s ->
        s to async(pool) {
            if (s is State.Interior) {
                (1..timeBound).step(18).all { t ->
                    val r = Rect(
                            tX[encoder.lowerThreshold(s.rectangle, 0)] to tX[encoder.upperThreshold(s.rectangle, 0)],
                            tY[encoder.lowerThreshold(s.rectangle, 1)] to tY[encoder.upperThreshold(s.rectangle, 1)]
                    )
                    modelFactory.run {
                        val flowQuery = makeQuery(
                                """
                        ${makeHead()}
                        ${makeHead("_0_0")}
                        ${makeHead("_0_t")}
                        (declare-fun time () Real [0.0, $t])
                        ${makeFixedFlow(0.012)}
                        (assert (= time $t))
                        (assert (= [x_0_t y_0_t] (integral 0. time [x_0_0 y_0_0] flow_1)))
                        ${r.boundsQuery("x_0_0", "y_0_0")}
                        ${r.boundsQuery("x_0_t", "y_0_t")}
                        (assert (forall_t 1 [0 time] (and (< x_0_t ${r.x2}) (> x_0_t ${r.x1}) (< y_0_t ${r.y2}) (> y_0_t ${r.y1}))))
                    """
                        )
                        try {
                            !checkNotSat(flowQuery).also {
                                println("time: $t is $it")
                            }
                        } catch (e: Exception) {
                            println(flowQuery)
                            throw e
                        }
                    }
                }
            } else if (s !is State.Transition || s.from == null || s.to == null) {
                true
            } else {
                val inequality = when {
                    encoder.upperThreshold(s.from, 0) == encoder.lowerThreshold(s.to, 0) -> {
                        // X dim aligned, upper facet
                        val eq = modelFactory.makeModelEquation(0)
                                .replace("x", tX[encoder.upperThreshold(s.from, 0)].toString())
                        """
                        (declare-fun y () Real [${tY[encoder.lowerThreshold(s.from, 1)]}, ${tY[encoder.upperThreshold(s.from, 1)]}])
                        (assert (<= 0.0 $eq))
                        """
                    }
                    encoder.lowerThreshold(s.from, 0) == encoder.upperThreshold(s.to, 0) -> {
                        // X dim aligned, lower facet
                        val eq = modelFactory.makeModelEquation(0)
                                .replace("x", tX[encoder.lowerThreshold(s.from, 0)].toString())
                        """
                        (declare-fun y () Real [${tY[encoder.lowerThreshold(s.from, 1)]}, ${tY[encoder.upperThreshold(s.from, 1)]}])
                        (assert (>= 0.0 $eq))
                        """
                    }
                    encoder.upperThreshold(s.from, 1) == encoder.lowerThreshold(s.to, 1) -> {
                        // Y dim aligned, upper facet
                        val eq = modelFactory.makeModelEquation(1)
                                .replace("y", tY[encoder.upperThreshold(s.from, 1)].toString())
                        """
                        (declare-fun x () Real [${tX[encoder.lowerThreshold(s.from, 0)]}, ${tX[encoder.upperThreshold(s.from, 0)]}])
                        (assert (<= 0.0 $eq))
                        """
                    }
                    encoder.lowerThreshold(s.from, 1) == encoder.upperThreshold(s.to, 1) -> {
                        // Y dim aligned, lower facet
                        val eq = modelFactory.makeModelEquation(1)
                                .replace("y", tY[encoder.lowerThreshold(s.from, 1)].toString())
                        """
                        (declare-fun x () Real [${tX[encoder.lowerThreshold(s.from, 0)]}, ${tX[encoder.upperThreshold(s.from, 0)]}])
                        (assert (>= 0.0 $eq))
                        """
                    }
                    else -> ""
                }
                val query = makeQuery(inequality)
                //if ((s.from == 122 || s.to == 122) && inequality.isEmpty()) println("Empty for $s")
                if (s.from == FIND || s.to == FIND) println(query)
                try {
                    !checkNotSat(query)
                } catch (e: Exception) {
                    println(query)
                    throw e
                }
            }
        }
    }.filter { it.also { println(it.first) }.second.await() }.map { it.first }

    val admissibleTransitions = transitions.filterKeys { it in admissibleStates }.mapValues { (_, succ) ->
        succ.filter { it in admissibleStates }
    }

    println("REMOVING USELESS TRANSITIONS")

    val actuallyReachable = admissibleTransitions.mapValues { (s, succ) ->
        if (s is State.Transition && s.from != null && s.to != null) {
            if (State.Interior(s.to) !in admissibleStates) {
                succ.filter { dest ->
                    dest !is State.Transition || dest.from == null || dest.to == null || kotlin.run {
                        modelFactory.run {
                            val reachQuery = makeQuery("""
                                    ${makeHead()}
                                    ${makeHead("_0_0")}
                                    ${makeHead("_0_t")}
                                    (declare-fun time () Real [0.0, $timeBound])
                                    ${makeFixedFlow(0.012)}
                                    (assert (= [x_0_t y_0_t] (integral 0. time [x_0_0 y_0_0] flow_1)))
                                    (assert ${s.getBounds(tX, tY, encoder).replace("x", "x_0_0").replace("y", "y_0_0")})
                                    (assert ${dest.getBounds(tX, tY, encoder).replace("x", "x_0_t").replace("y", "y_0_t")})
                                """)
                            //TODO: Check that the trajectory is fully contained.
                            try {
                                !checkNotSat(reachQuery).also {
                                    println("Transition allowed: ${!it}")
                                }
                            } catch (e: Exception) {
                                println(reachQuery)
                                throw e
                            }
                        }
                    }
                }
            } else succ
        } else succ
    }

    //return DeltaModel(states, (enteringSystem + exitingInterior + exitingEdge).toMap())
    return DeltaModel(admissibleStates, actuallyReachable)
}

fun State.Transition.getBounds(tX: List<Double>, tY: List<Double>, encoder: NodeEncoder): String {
    from!!
    to!!
    return when {
        encoder.upperThreshold(from, 0) == encoder.lowerThreshold(to, 0) -> {
            // X dim aligned, upper facet
            "(and (= x ${tX[encoder.upperThreshold(from, 0)]}) (<= y ${tY[encoder.upperThreshold(from, 1)]}) (>= y ${tY[encoder.lowerThreshold(from, 1)]}))"
        }
        encoder.lowerThreshold(from, 0) == encoder.upperThreshold(to, 0) -> {
            // X dim aligned, lower facet
            "(and (= x ${tX[encoder.lowerThreshold(from, 0)]}) (<= y ${tY[encoder.upperThreshold(from, 1)]}) (>= y ${tY[encoder.lowerThreshold(from, 1)]}))"
        }
        encoder.upperThreshold(from, 1) == encoder.lowerThreshold(to, 1) -> {
            // Y dim aligned, upper facet
            "(and (= y ${tY[encoder.upperThreshold(from, 1)]}) (<= x ${tX[encoder.upperThreshold(from, 0)]}) (>= x ${tX[encoder.lowerThreshold(from, 0)]}))"
        }
        encoder.lowerThreshold(from, 1) == encoder.upperThreshold(to, 1) -> {
            // Y dim aligned, lower facet
            "(and (= y ${tY[encoder.upperThreshold(from, 0)]}) (<= x ${tX[encoder.upperThreshold(from, 0)]}) (>= x ${tX[encoder.lowerThreshold(from, 0)]}))"
        }
        else -> error("Rectangles $from and $to not connected")
    }
}

