package dreal

import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.OdeModel

/**
 * A generic variant of a transition system represented using a set of states and a list of edges.
 */
data class TransitionSystem<out T: Any>(
        val states: List<T>,
        val edges: List<Pair<Int, Int>>
)

/**
 * Export a classic rectangular transition system information.
 */
fun OdeModel.exportTransitionSystem(): TransitionSystem<Int> {
    RectangleOdeModel(this, true).run {
        val states = (0 until stateCount).toList()

        val edges = (0 until stateCount).flatMap { s ->
            s.successors(true).asSequence().map { s to it.target }.toList()
        }

        return TransitionSystem(states, edges)
    }
}