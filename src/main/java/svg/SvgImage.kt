package svg

import java.io.Writer

data class SvgImage(
        val primitives: List<SvgPrimitive<*>>,
        val arrowSize: Double
) {

    private val dimensions: Point
    private val down: Point
    private val up: Point

    init {
        var minX = 0.0 ; var minY = 0.0
        var maxX = 0.0 ; var maxY = 0.0
        primitives.asSequence().flatMap { it.anchors }.forEach { (x,y) ->
            if (x > maxX) maxX = x
            if (x < minX) minX = x
            if (y > maxY) maxY = y
            if (y < minY) minY = y
        }
        up = xy(maxX, maxY)
        down = xy(minX, minY)
        dimensions = up + (down * -1.0)
    }

    operator fun plus(other: SvgImage): SvgImage {
        return SvgImage(primitives + other.primitives, Math.min(arrowSize, other.arrowSize))
    }

    /**
     * Scale and offset this SVG image to target width, preserving the aspect ratio and making everything visible.
     */
    fun normalize(targetWidth: Double? = null): SvgImage {
        val delta = down * -1.0
        val factor = if (targetWidth != null) targetWidth / dimensions.y else 1.0
        // the order of transformations is important!
        return copy(primitives = primitives.map { it.translate(delta).flipY(dimensions.y).scale(factor) }, arrowSize = arrowSize * factor)
    }

    fun writeTo(writer: Writer) = writer.run {
        appendln(svgPrefix())
        primitives.forEach {
            appendln(it.compileSvg())
        }
        appendln(svgSuffix())
    }

    fun compileSvg(): String = buildString {
        appendln(svgPrefix())
        primitives.forEach {
            appendln(it.compileSvg())
        }
        appendln(svgSuffix())
    }

    private fun svgPrefix(): String =
"""<?xml version="1.0" standalone="no"?>
<svg width="${dimensions.x}" height="${dimensions.y}" version="1.1" xmlns="http://www.w3.org/2000/svg">
    <defs>
        <marker id="arrow" markerWidth="$arrowSize" markerHeight="$arrowSize" refX="$arrowSize" refY="${arrowSize/2}" orient="auto" markerUnits="strokeWidth">
            <path d="M0,0 L0,$arrowSize L$arrowSize,${arrowSize/2} z" fill="#000" />
        </marker>
    </defs>
"""

    private fun svgSuffix(): String =
"""
</svg>
"""

}