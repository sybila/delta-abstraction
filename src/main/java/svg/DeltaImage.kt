package svg

import dreal.Partitioning
import dreal.State
import dreal.TransitionSystem

data class DeltaImage(
        private val partitioning: Partitioning,
        private val system: TransitionSystem<State>,
        private val property: Set<State>
) : Image {

    override fun toSvgImage(): SvgImage {
        val rectangles = partitioning.items.map { it.bounds }
        val partitionRectangles = rectangles.map { r ->
            val isColored = property.any { (it is State.Interior && it.rectangle == r) || (it is State.Transition && it.to == r) }
            r.toSvgRectangle().copy(style = Style.STROKE.fillColor(if (isColored) "#aaaaff" else "#ffffff"))
        }

        val partitionLabels = emptyList<SvgPrimitive<*>>()/*rectangles.mapIndexed { i, r ->
            Text(i.toString(), r.toSvgRectangle().center)
        }*/

        val arrowSize = partitionRectangles.map { it.dimensions.x }.average() / 2.0

        val states: Map<State, Circle?> = system.states.map { s ->
            s to when (s) {
                is State.Interior -> {
                    val rectangle = s.rectangle.toSvgRectangle()
                    Circle(rectangle.center, Math.min(rectangle.width, rectangle.height) * 0.125, Style.FILL)
                }
                is State.Transition -> {
                    try {
                        val (_, dimension, positive) = s.from.getFacetIntersection(s.to)!!
                        val rectangle = s.via
                        val d = if (dimension == 0) Dimension.Y else Dimension.X    // sliding dimension is the opposite of contact dimension
                        val r = rectangle.toSvgRectangle()
                        val center = if (State.Transition(s.to, s.from, s.via) !in system.states) r.center else {
                            r.innerPoint(d, if (positive) 0.33 else 0.66)
                        }
                        val radius = (if (dimension == 0) r.height else r.width) * 0.1
                        Circle(center, radius, Style.STROKE.fillColor("#ffffff"))
                    } catch (e: RuntimeException) { null /* Well, tough luck */ }
                }
                is State.Exterior -> null
            }
        }.toMap()

        // WARNING: We are not drawing the exterior state, so some transitions will not be drawn!

        val transitions = system.edges.mapNotNull { (source, destination) ->
            if (source == destination) null else {
                val from = states[system.states[source]]
                val to = states[system.states[destination]]
                if (from == null || to == null) null else {
                    val (a, b) = from.anchors.flatMap { a ->
                        to.anchors.map { b -> a to b }
                    }.minBy { (a, b) -> a.distanceTo(b) }!!
                    Line(a, b, Style.ARROW.strokeWidth(0.5))
                }
            }
        }

        return SvgImage(partitionRectangles + partitionLabels + states.values.filterNotNull() + transitions, arrowSize)
    }

}

