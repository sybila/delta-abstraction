package svg

import dreal.DeltaModel
import dreal.State
import dreal.project.Partitioning
import dreal.project.TransitionSystem

data class DeltaImage(
        private val partitioning: Partitioning,
        private val system: TransitionSystem<State>,
        private val property: Set<State>
) {

    fun toSvgImage(): SvgImage {
        val rectangles = partitioning.items.map { it.bounds }
        val partitionRectangles = rectangles.map { r ->
            val isColored = property.any { (it is State.Interior && it.rectangle == r) || (it is State.Transition && it.to == r) }
            r.toSvgRectangle().copy(style = Style.STROKE.fillColor(if (isColored) "#aaaaff" else "#ffffff"))
        }
        val arrowSize = partitionRectangles.map { it.dimensions.x }.average() / 5.0

        val states: Map<State, Circle?> = system.states.map { s ->
            s to when (s) {
                is State.Interior -> {
                    val rectangle = s.rectangle.toSvgRectangle()
                    Circle(rectangle.center, Math.min(rectangle.width, rectangle.height) * 0.125, Style.FILL)
                }
                is State.Transition -> {
                    run {
                        val (rectangle, dimension, positive) = s.from.getFacetIntersection(s.to)!!
                        val d = if (dimension == 0) Dimension.Y else Dimension.X    // sliding dimension is the opposite of contact dimension
                        val r = rectangle.toSvgRectangle()
                        val center = if (State.Transition(s.to, s.from) !in system.states) r.center else {
                            r.innerPoint(d, if (positive) 0.33 else 0.66)
                        }
                        val radius = (if (dimension == 0) r.height else r.width) * 0.1
                        Circle(center, radius, Style.STROKE.fillColor(if (s in property) "#aaaaff" else "#ffffff"))
                    }
                }
                else -> null
            }
        }.toMap()

        val transitions = system.edges.mapNotNull { (source, destination) ->
            if (source == destination) null else {
                val from = states[system.states[source]]!!
                val to = states[system.states[destination]]!!
                val (a, b) = from.anchors.flatMap { a ->
                    to.anchors.map { b -> a to b }
                }.minBy { (a, b) -> a.distanceTo(b) }!!
                Line(a, b, Style.ARROW.strokeWidth(0.5))
            }
        }

        return SvgImage(partitionRectangles + states.values.filterNotNull() + transitions, arrowSize)
    }

}

