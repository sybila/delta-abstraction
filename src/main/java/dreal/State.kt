package dreal

sealed class State {

    /**
     * Abstract state representing the trajectories outside of the system bounds.
     */
    object Exterior : State() {
        override fun contains(dim: Int, value: Double): Boolean = false
        override fun project(dim: Int): State = this
    }

    /**
     * Abstract state representing the interior trajectories of given [rectangle].
     */
    data class Interior(val rectangle: Rectangle) : State() {

        override fun contains(dim: Int, value: Double): Boolean
            = error("")// rectangle.contains(dim, value)

        override fun project(dim: Int): State
            = Interior(rectangle.project(dim))
    }

    /**
     * Abstract state representing trajectories flowing [from] one given rectangle [to] the other one.
     */
    data class Transition(val from: Rectangle, val to: Rectangle, val via: Rectangle) : State() {

        override fun contains(dim: Int, value: Double): Boolean
                = error("") //via.contains(dim, value)

        override fun project(dim: Int): State
                = Transition(from.project(dim), to.project(dim), via.project(dim))
    }


    abstract fun contains(dim: Int, value: Double): Boolean

    abstract fun project(dim: Int): State

}