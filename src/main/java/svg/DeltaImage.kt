package svg

import dreal.DeltaModel
import dreal.State

data class DeltaImage(
        private val model: DeltaModel,
        private val property: Set<State>
) {

    fun toSvgImage(): SvgImage {
        val partitionRectangles = model.partitioning.rectangles.map { (r, _) ->
            val isColored = property.any { (it is State.Interior && it.rectangle == r) || (it is State.Transition && it.to == r) }
            r.toSvgRectangle().copy(style = Style.STROKE.fillColor(if (isColored) "#aaaaff" else "#ffffff"))
        }
        val arrowSize = partitionRectangles.map { it.dimensions.x }.average() / 5.0

        val states: Map<State, Circle?> = model.states.map { s ->
            s to when (s) {
                is State.Interior -> {
                    val rectangle = s.rectangle.toSvgRectangle()
                    Circle(rectangle.center, Math.min(rectangle.width, rectangle.height) * 0.125, Style.FILL)
                }
                is State.Transition -> {
                    if (s.to == null || s.from == null) null else {
                        val (rectangle, dimension, positive) = s.from.getFacetIntersection(s.to)!!
                        val d = if (dimension == 0) Dimension.Y else Dimension.X    // sliding dimension is the opposite of contact dimension
                        val r = rectangle.toSvgRectangle()
                        val center = if (State.Transition(s.to, s.from) !in model.states) r.center else {
                            r.innerPoint(d, if (positive) 0.33 else 0.66)
                        }
                        val radius = (if (dimension == 0) r.height else r.width) * 0.1
                        Circle(center, radius, Style.STROKE.fillColor(if (s in property) "#aaaaff" else "#ffffff"))
                    }
                }
                else -> null
            }
        }.toMap()

        val transitions = model.transitions.flatMap { (source, destinations) ->
            states[source]?.let { from ->
                destinations.filter { it != source }.mapNotNull { states[it] }.map { to ->
                    val (a, b) = from.anchors.flatMap { a -> to.anchors.map { b -> a to b } }.minBy { (a, b) -> a.distanceTo(b) }!!
                    Line(a, b, Style.ARROW.strokeWidth(0.5))
                }
            } ?: emptyList()
        }

        return SvgImage(partitionRectangles + states.values.filterNotNull() + transitions, arrowSize)

/*

        val tX = ode.variables[0].thresholds
        val tY = ode.variables[1].thresholds
        val encoder = NodeEncoder(ode)

        fun NodeEncoder.makeRectangle(s: Int): Rectangle {
            val (x, y) = decodeNode(s)
            val rectangleWidth = tX[x+1] - tX[x]
            val rectangleHeight = tY[y+1] - tY[y]
            return Rectangle(  center = xy(tX[x] + rectangleWidth / 2.0, tY[y] + rectangleHeight / 2.0),
                    dimensions = xy(rectangleWidth, rectangleHeight),
                    style = Style.STROKE
            )
        }

        fun State.Transition.findAnchorPoint(): Point {
            return if (from != null && to != null) {
                // Find anchor which is closest to the middle point of the two rectangles.
                // Should land you in the middle of the connecting facet.
                val rFrom = encoder.makeRectangle(from)
                val rTo = encoder.makeRectangle(to)
                val middlePoint = (rFrom.center + rTo.center) * 0.5
                (rFrom.anchors + rTo.anchors).minBy { it.distanceTo(middlePoint) }!!
            } else if (from != null || to != null) {
                // There is just one rectangle. We select the border anchors which connect to outside world.
                // Then we select the closest anchor which should land us in the middle of the facet.
                // In corners, this might not work, because we can have several closest anchors.
                // Then we select the one in the corner.
                val state = from ?: to!!
                encoder.makeRectangle(state).run {
                    val borderAnchors = buildSequence {
                        if (encoder.lowerNode(state, 0) == null) {
                            yieldAll(sequenceOf(leftDown, leftUp))
                        }
                        if (encoder.lowerNode(state, 1) == null) {
                            yieldAll(sequenceOf(leftDown, rightDown))
                        }
                        if (encoder.higherNode(state, 0) == null) {
                            yieldAll(sequenceOf(rightDown, rightUp))
                        }
                        if (encoder.higherNode(state, 1) == null) {
                            yieldAll(sequenceOf(leftUp, rightUp))
                        }
                    }.toList()
                    val middlePoint = borderAnchors.fold(Point.ZERO, Point::plus) * (1.0/borderAnchors.size)
                    val minDistance = anchors.map { it.distanceTo(middlePoint) }.min()!!
                    val closestAnchors = anchors.filter { it.distanceTo(middlePoint) == minDistance }.toList()
                    if (closestAnchors.size == 1) closestAnchors[0] else {
                        val preferred = listOf(leftDown, leftUp, rightUp, rightDown)
                        closestAnchors.firstOrNull { it in preferred } ?: closestAnchors[closestAnchors.size / 2]
                    }
                }
            } else {
                error("State.Transition(null, null) not allowed.")
            }
        }

        fun State.Transition.findStateSize(): Double {
            return buildSequence<Double> {
                yieldAll(from?.let { encoder.makeRectangle(it).sizes } ?: emptySequence())
                yieldAll(to?.let { encoder.makeRectangle(it).sizes } ?: emptySequence())
            }.min()!! / 10.0
        }

        // Set arrow size as 1/10th of average rectangle size in X dimension.
        val boundsX = tX.dropLast(1).zip(tX.drop(1))
        val arrowSize = boundsX.map { (l, h) -> h - l }.average() / 5.0

        // Draw rectangular grid.
        val gridX = tX.map { x ->
            Line(xy(x, tY.first()), xy(x, tY.last()), Style.STROKE)
        }
        val gridY = tY.map { y ->
            Line(xy(tX.first(), y), xy(tX.last(), y), Style.STROKE)
        }

        val states = model.states.map { s ->
            when (s) {
                is State.Interior -> {
                    // create interior circles
                    val (x, y) = encoder.decodeNode(s.rectangle)
                    val rectangleWidth = tX[x+1] - tX[x]
                    val rectangleHeight = tY[y+1] - tY[y]
                    Circle( center = xy(tX[x] + rectangleWidth / 2.0, tY[y] + rectangleHeight / 2.0),
                            radius = Math.min(rectangleWidth, rectangleHeight) / 8.0,
                            style = Style.STROKE.fillColor(if (s in property) "#ff0000" else "#000000")
                    )
                }
                is State.Transition -> when {
                    State.Transition(s.to, s.from) !in model.states -> {
                        // There's going to be just one state on that edge, so we're good.
                        Circle( center = s.findAnchorPoint(), radius = s.findStateSize(),
                                style = Style.STROKE.fillColor(if (s in property) "#ff0000" else if (s.from == FIND || s.to == FIND) "#000000" else "#ffffff")
                        )
                    }
                    else -> {
                        // There are two states, so we have to place them on the secondary anchors.
                        val stateAnchor = s.findAnchorPoint()
                        val index = when {
                            s.from != null && s.to != null && s.from < s.to -> 1
                            s.from != null && s.to != null -> 0
                            s.from != null -> 1
                            s.to != null -> 0
                            else -> 0
                        }
                        val candidates = encoder.makeRectangle(s.from ?: s.to!!).secondaryAnchors
                                .sortedBy { it.distanceTo(stateAnchor) }.take(2).sorted().toList()
                        Circle( center = candidates[index], radius = s.findStateSize(),
                                style = Style.STROKE.fillColor(if (s in property) "#ff0000" else if (s.from == FIND || s.to == FIND) "#000000" else "#ffffff")
                        )
                    }
                }
                else -> null
            }
        }

        val stateMapping = model.states.zip(states).toMap()

        val transitions = model.transitions.flatMap { (source, destinations) ->
            stateMapping[source]?.let { from ->
                destinations.map { destination ->
                    stateMapping[destination]?.let { to ->
                        val (a, b) = from.anchors.flatMap { a -> to.anchors.map { b -> a to b } }.minBy { (a, b) -> a.distanceTo(b) }!!
                        Line(a, b, Style.ARROW.strokeWidth(0.5))
                    }
                }
            } ?: emptyList()
        }.filterNotNull()

        return SvgImage( transitions + gridX + gridY + states.filterNotNull(), arrowSize = arrowSize)*/
    }

}

