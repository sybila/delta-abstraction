import Dimension.X
import Dimension.Y
import java.io.BufferedWriter
import java.io.File
import java.util.*

enum class Dimension { X, Y }

data class Point(val x: Double, val y: Double) {

    operator fun plus(other: Point) = Point(x + other.x, y + other.y)

    operator fun times(num: Double) = Point(x * num, y * num)

    fun flipY(height: Double) = Point(x, height - y)

}

data class Style(val properties: Map<String, String>) {
    companion object {
        val DEFAULT = Style(emptyMap())
        val STROKE = Style(mapOf("stroke-width" to "1", "stroke" to "black", "fill" to "transparent"))
        val FILL = Style(mapOf("fill" to "black"))
    }

    fun writeSVG(): String = buildString {
        for ((key, value) in properties) {
            append("$key=\"$value\" ")
        }
    }
}

data class Rectangle(val bottom: Point, val top: Point, val style: Style = Style.DEFAULT) {

    fun getEdge(d: Dimension, up: Boolean): Pair<Point, Point> = when {
        d == X && !up -> bottom to top.copy(x = bottom.x)
        d == X && up -> bottom.copy(x = top.x) to top
        d == Y && !up -> bottom to top.copy(y = bottom.y)
        d == Y && up -> bottom.copy(y = top.y) to top
        else -> error("unreachable")
    }

    val center: Point
        get() = middle(bottom, top)

    fun writeSVG(writer: BufferedWriter) = writer.run {
        appendln("<rect x=\"${bottom.x}\" y=\"${bottom.y}\" width=\"${top.x - bottom.x}\" height=\"${top.y - bottom.y}\" ${style.writeSVG()}/>")
    }

    inline fun map(action: (Point) -> Point): Rectangle = Rectangle(action(bottom), action(top), style)

    fun flipY(height: Double): Rectangle {
        val bY = bottom.y
        val tY = top.y
        return copy(bottom = bottom.copy(y = height - tY), top = top.copy(y = height - bY))
    }

}

data class Circle(val middle: Point, val radius: Double, val style: Style = Style.DEFAULT) {

    fun getBoundaryPoint(d: Dimension, up: Boolean): Point = when (d) {
        X -> middle.copy(x = middle.x + if (up) radius else -radius)
        Y -> middle.copy(y = middle.y + if (up) radius else -radius)
    }

}

data class Arrow(val start: Point, val stop: Point, val style: Style = Style.DEFAULT)

fun xy(x: Double, y: Double) = Point(x,y)

fun middle(a: Point, b: Point) = Point((a.x + b.x) / 2.0,(a.y + b.y) / 2.0)

fun Pair<Double, Double>.toPoint() = Point(first, second)

fun Pair<Point, Point>.middle(): Point = middle(first, second)

fun Pair<Point, Point>.lowThird(): Point = Point(
        (this.first.x + this.second.x) / 3.0,
        (this.first.y + this.second.y) / 3.0
)

fun Pair<Point, Point>.highThird(): Point = Point(
        ((this.first.x + this.second.x) / 3.0) * 2.0,
        ((this.first.y + this.second.y)) / 3.0 * 2.0
)


data class PWMA_StateSpace(
        val states: List<Rectangle>,
        val transitions: List<Transition>
) {

    data class Transition(
            val from: Rectangle, val to: Rectangle
    )

    fun writeSVG(writer: BufferedWriter, targetWidth: Double? = null) = writer.run {
        val (minX, minY) = states.map { it.bottom }.run {
            map { it.x }.min()!! to map { it.y }.min()!!
        }
        val (maxX, maxY) = states.map { it.top }.run {
            map { it.x }.max()!! to map { it.y }.max()!!
        }

        val width = maxX - minX
        val height = maxY - minY

        val scaleFactor = (targetWidth ?: width) / width
        val shift = Point(-minX, -minY)

        appendln("<?xml version=\"1.0\" standalone=\"no\"?>")
        appendln("<svg width=\"${width * scaleFactor}\" height=\"${height * scaleFactor}\" version=\"1.1\" xmlns=\"http://www.w3.org/2000/svg\">")

        states.forEach {
            it.map { it + shift }.flipY(height).map { it * scaleFactor }.writeSVG(this)
        }

        appendln("</svg>")
    }

}

inline fun SVG(width: Double, height: Double, builder: SvgBuilder.() -> Unit): String {
    return SvgBuilder(width, height).apply(builder).build()
}

class SvgBuilder(private val width: Double, private val height: Double) {

    private val items = ArrayList<String>()

    fun addRectangleRelative(x: Double, y: Double, dx: Double, dy: Double, fill: Double = 0.0) {
        items.add("""<rect x="$x" y="${height - y - dy}" width="$dx" height="$dy" fill-opacity="$fill" fill="black" stroke-width="1" stroke="black"/>""")
    }

    fun addRectangle(x1: Double, y1: Double, x2: Double, y2: Double, fill: Double = 0.0)
        = addRectangleRelative(x1, y1, Math.abs(x1 - x2), Math.abs(y1 - y2), fill)

    fun build(): String =
"""
<?xml version="1.0" standalone="no"?>
<svg width="$width" height="$height" version="1.1" xmlns="http://www.w3.org/2000/svg">
${items.joinToString(separator = "\n")}
</svg>
""".trim()

}

fun main(args: Array<String>) {
    val f = File("/Users/daemontus/Downloads/test.svg")
    val system = PWMA_StateSpace(
            (-5..5).flatMap { x ->
                (-3..4).map { y ->
                    Rectangle(xy(x.toDouble(), y.toDouble()), xy(x + 1.0, y + 1.0), Style.STROKE)
                }
            }
            /*listOf(
                    Rectangle(xy(-1.0, -1.0), xy(0.0, 0.0), Style.STROKE),
                    Rectangle(xy(0.0, -1.0), xy(1.0, 0.0), Style.STROKE),
                    Rectangle(xy(-1.0, 0.0), xy(0.0, 1.0), Style.STROKE),
                    Rectangle(xy(0.0, 0.0), xy(1.0, 1.0), Style.STROKE)
            )*/, listOf()
    )
    f.bufferedWriter().use {
        system.writeSVG(it, targetWidth = 1000.0)
    }
}