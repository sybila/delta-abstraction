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
        val encoder = NodeEncoder(ode)

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

        // Draw state circles, possibly with self-loops.
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

        // Draw transitions between closest anchor of each state.
        val transitions = (0 until stateCount).flatMap { s ->
            s.successors(true).asSequence().map { (t, _, _) ->
                if (s == t) null else {
                    val from = states[s]
                    val to = states[t]
                    val (a, b) = from.anchors.flatMap { a -> to.anchors.map { b -> a to b } }.minBy { (a, b) -> a.distanceTo(b) }!!
                    Line(a, b, Style.ARROW.strokeWidth(0.5))
                }
            }.filterNotNull().toList()
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