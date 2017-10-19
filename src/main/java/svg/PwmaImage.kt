package svg

import com.github.sybila.ode.generator.NodeEncoder
import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.OdeModel

data class PwmaImage(
        val ode: OdeModel,
        val model: RectangleOdeModel,
        val property: Map<String, Set<Int>>
) {

    fun toSvgImage(): SvgImage = model.run {
        val tX = ode.variables[0].thresholds
        val tY = ode.variables[1].thresholds

        val boundsX = tX.dropLast(1).zip(tX.drop(1))
        val boundsY = tY.dropLast(1).zip(tY.drop(1))

        // set arrow size as 1/10th of average rectangle size in X dimension.
        val arrowSize = boundsX.map { (l, h) -> h - l }.average() / 5.0
        val gridX = tX.map { x ->
            Line(xy(x, tY.first()), xy(x, tY.last()), Style.STROKE)
        }
        val gridY = tY.map { y ->
            Line(xy(tX.first(), y), xy(tX.last(), y), Style.STROKE)
        }

        val encoder = NodeEncoder(ode)
        val states = (0 until stateCount).map { s ->
            // create circles
            val (x, y) = encoder.decodeNode(s)
            val rectangleWidth = tX[x+1] - tX[x]
            val rectangleHeight = tY[y+1] - tY[y]
            Circle( center = xy(tX[x] + rectangleWidth / 2.0, tY[y] + rectangleHeight / 2.0),
                    radius = Math.min(rectangleWidth, rectangleHeight) / 6.0,
                    style = Style.STROKE
            )
        }.mapIndexed { s, circle ->
            // handle self loops
            if (s.successors(true).asSequence().any { it.target == s }) {
                circle.copy(style = Style.FILL)
            } else {
                circle
            }
        }

        val transitions = (0 until stateCount).flatMap { s ->
            s.successors(true).asSequence().map { (t, _, _) ->
                val from = states[s]
                val to = states[t]
                val (a, b) = from.anchors.flatMap { a -> to.anchors.map { b -> a to b } }.minBy { (a, b) -> a.distanceTo(b) }!!
                Line(a, b, Style.ARROW.strokeWidth(0.5))
            }.toList()
        }

        val properties = property.flatMap { (color, states) ->
            states.map { s ->
                // create rectangles
                val (x, y) = encoder.decodeNode(s)
                val rectangleWidth = tX[x+1] - tX[x]
                val rectangleHeight = tY[y+1] - tY[y]
                Rectangle(  center = xy(tX[x] + rectangleWidth / 2.0, tY[y] + rectangleHeight / 2.0),
                            dimensions = xy(rectangleWidth, rectangleHeight),
                            style = Style.FILL.fillColor(color)
                )
            }
        }

        return SvgImage(properties + gridX + gridY + states + transitions, arrowSize = arrowSize)
    }

}