package dreal

import com.github.sybila.ode.generator.NodeEncoder
import com.github.sybila.ode.model.OdeModel
import kotlinx.coroutines.experimental.runBlocking
import kotlin.coroutines.experimental.buildSequence

fun main(args: Array<String>) {
    runBlocking {
        G1Sswitch.makePartitions()
    }
}

fun OdeModel.makeDeltaAbstraction(): DeltaModel {

    val encoder = NodeEncoder(this)

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

    // check state admissibility
    val admissibleStates = states.map { s ->
        s to
    }


    return DeltaModel(states, (enteringSystem + exitingInterior + exitingEdge).toMap())
}

