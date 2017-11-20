package dreal.project

import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.OdeModel

data class TransitionSystem<out T: Any>(
        val states: List<T>,
        val edges: List<Pair<Int, Int>>
)

fun OdeModel.exportTransitionSystem(): TransitionSystem<Int> {
    RectangleOdeModel(this, true).run {
        val states = (0 until stateCount).toList()

        val edges = (0 until stateCount).flatMap { s ->
            s.successors(true).asSequence().map { s to it.target }.toList()
        }

        return TransitionSystem(states, edges)
    }
}