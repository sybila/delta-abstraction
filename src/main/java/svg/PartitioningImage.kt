package svg

import dreal.Partitioning

fun Partitioning.toSvgImage(property: Set<dreal.Rectangle> = emptySet()): SvgImage {
    val rectangles = items.map { (r, _) ->
        val color = if (r in property) "#aaaaff" else "transparent"
        r.toSvgRectangle().copy(style = Style.STROKE.fillColor(color))
    }

    val arrowSize = rectangles.map { it.dimensions.x }.average() / 5.0

    return SvgImage(rectangles, arrowSize)
}