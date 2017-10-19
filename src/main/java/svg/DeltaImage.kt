package svg

import com.github.sybila.ode.generator.NodeEncoder
import com.github.sybila.ode.model.OdeModel
import dreal.DeltaModel
import dreal.State

data class DeltaImage(
        val ode: OdeModel,
        val model: DeltaModel,
        val properties: Map<String, Set<State>>
) {

    fun toSvgImage(): SvgImage {
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

        val states: List<SvgPrimitive<*>> = model.states.mapIndexed { i, s ->
            when (s) {
                is State.Interior -> {
                    // create interior circles
                    val (x, y) = encoder.decodeNode(s.rectangle)
                    val rectangleWidth = tX[x+1] - tX[x]
                    val rectangleHeight = tY[y+1] - tY[y]
                    Circle( center = xy(tX[x] + rectangleWidth / 2.0, tY[y] + rectangleHeight / 2.0),
                            radius = Math.min(rectangleWidth, rectangleHeight) / 8.0,
                            style = Style.STROKE
                    )
                }
                is State.Transition -> when {
                    s.from != null && s.to != null -> {
                        val (fX, fY) = encoder.decodeNode(s.from)
                        val (tX, tY) = encoder.decodeNode(s.to)
                        
                        null
                    }
                    else -> null
                }
                else -> null
            }
        }.filterNotNull()

        return SvgImage( gridX + gridY + states, arrowSize = arrowSize)
    }

}