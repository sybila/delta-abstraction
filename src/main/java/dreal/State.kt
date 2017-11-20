package dreal

sealed class State {

    /**
     * Abstract state representing the trajectories outside of the system bounds.
     */
    object Exterior : State()

    /**
     * Abstract state representing the interior trajectories of given [rectangle].
     */
    data class Interior(val rectangle: Rectangle) : State()

    /**
     * Abstract state representing trajectories flowing [from] one given rectangle [to] the other one.
     */
    data class Transition(val from: Rectangle, val to: Rectangle) : State()

}