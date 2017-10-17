import Dimension.X
import Dimension.Y
import com.github.sybila.ode.generator.NodeEncoder
import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.Parser
import java.io.BufferedWriter
import java.io.File
import kotlin.collections.ArrayList
import kotlin.collections.HashSet

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

    val width: Double
        get() = top.x - bottom.x

    val height: Double
        get() = top.y - bottom.y

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

    fun writeSVG(writer: BufferedWriter) = writer.run {
        appendln("<circle cx=\"${middle.x}\" cy=\"${middle.y}\" r=\"$radius\" ${style.writeSVG()}/>")
    }

    fun flipY(height: Double): Circle {
        val newY = middle.y
        return copy(middle = middle.copy(y = newY))
    }

}

data class Arrow(val start: Point, val stop: Point, val style: Style = Style.DEFAULT) {

    fun writeSVG(writer: BufferedWriter) = writer.run {
        appendln("<line x1=\"${start.x}\" y1=\"${start.y}\" x2=\"${stop.x}\" y2=\"${stop.y}\" marker-end=\"url(#arrow)\" ${style.writeSVG()} />")
    }

}

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
        val transitions: List<Transition>,
        val highlight: List<Rectangle>
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
        val rectangleScale = states.first().width * scaleFactor * 1.5
        val shift = Point(-minX, -minY)

        appendln("<?xml version=\"1.0\" standalone=\"no\"?>")
        appendln("<svg width=\"${width * scaleFactor}\" height=\"${height * scaleFactor}\" version=\"1.1\" xmlns=\"http://www.w3.org/2000/svg\">")

        appendln(
"""
<defs>
    <marker id="arrow" markerWidth="${0.1 * rectangleScale}" markerHeight="${0.1 * rectangleScale}" refX="${0.09 * rectangleScale}" refY="${0.025 * rectangleScale}" orient="auto" markerUnits="strokeWidth">
        <path d="M0,0 L0,${0.05 * rectangleScale} L${0.09 * rectangleScale},${0.025 * rectangleScale} z" fill="#000" />
    </marker>
</defs>
""")

        fun Rectangle.toState(): Circle {
            val radius = Math.min(this.width, this.height) / 6.0;
            val style = if (Transition(this, this) in transitions) Style.FILL else Style.STROKE
            return Circle((center + shift).flipY(height) * scaleFactor, radius * scaleFactor, style)
        }

        states.forEach {
            it.map { it + shift }.flipY(height).map { it * scaleFactor }.copy(style = Style.STROKE).writeSVG(this)
        }

        val states = this@PWMA_StateSpace.states.map { it.toState() }
        val transitions = this@PWMA_StateSpace.transitions.map { (from, to) ->
            when {
                from.getEdge(X, true) == to.getEdge(X, false) -> Arrow(
                        from.toState().getBoundaryPoint(X, true),
                        to.toState().getBoundaryPoint(X, false), Style.STROKE
                )
                from.getEdge(X, false) == to.getEdge(X, true) -> Arrow(
                        from.toState().getBoundaryPoint(X, false),
                        to.toState().getBoundaryPoint(X, true), Style.STROKE
                )
                from.getEdge(Y, true) == to.getEdge(Y, false) -> Arrow(
                        from.toState().getBoundaryPoint(Y, false),
                        to.toState().getBoundaryPoint(Y, true), Style.STROKE
                )
                from.getEdge(Y, false) == to.getEdge(Y, true) -> Arrow(
                        from.toState().getBoundaryPoint(Y, true),
                        to.toState().getBoundaryPoint(Y, false), Style.STROKE
                )
                else -> null
            }
        }.filterNotNull()

        states.forEach {
            it.writeSVG(this)
        }

        transitions.forEach {
            it.writeSVG(this)
        }

        highlight.forEach {
            it.map { it + shift }.flipY(height).map { it * scaleFactor }.copy(style = Style.FILL).writeSVG(this)
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
    val input = File("/Users/daemontus/Downloads/test.bio")
    val f = File("/Users/daemontus/Downloads/test.svg")
    val thresholds = (0..50).map { it / 5.0 }
    val model = Parser().parse(input).let { m ->
        m.copy(variables = m.variables.map { v ->
            v.copy(thresholds = thresholds)
        })
    }

    //.computeApproximation(cutToRange = true)
    val ts = RectangleOdeModel(model, createSelfLoops = true)
    ts.run {
        val encoder = NodeEncoder(model)
        val states = (0 until stateCount).map { s ->
            Rectangle(
                    xy( model.variables[0].thresholds[encoder.lowerThreshold(s, 0)],
                        model.variables[1].thresholds[encoder.lowerThreshold(s, 1)]
                    ),
                    xy( model.variables[0].thresholds[encoder.upperThreshold(s, 0)],
                        model.variables[1].thresholds[encoder.upperThreshold(s, 1)]
                    )
            )
        }
        val transitions = (0 until stateCount).flatMap { s ->
            //println("$s: " + s.successors(true).asSequence().map { it.target }.toList())
            s.successors(true).asSequence().map {
                PWMA_StateSpace.Transition(states[s], states[it.target])
            }.toList()
        }
        val attractor = HashSet<Int>()
        for (s in (0 until stateCount)) {
            println(s)
            //bind s : AG EF s = ! EF ! EF s
            if (s in invert(fixedPoint(invert(fixedPoint(setOf(s)))))) {
                attractor.add(s)
            }
        }
        println("Attr: $attractor")
        f.bufferedWriter().use {
            PWMA_StateSpace(states, transitions, attractor.toList().map { states[it] }).writeSVG(it, targetWidth = 1000.0)
        }
    }
    /*
    val dd = Rectangle(xy(-1.0, -1.0), xy(0.0, 0.0), Style.STROKE)
    val dh = Rectangle(xy(0.0, -1.0), xy(1.0, 0.0), Style.STROKE)
    val hd = Rectangle(xy(-1.0, 0.0), xy(0.0, 1.0), Style.STROKE)
    val hh = Rectangle(xy(0.0, 0.0), xy(1.0, 1.0), Style.STROKE)
    val system = PWMA_StateSpace(
            /*(-5..5).flatMap { x ->
                (-3..4).map { y ->
                    Rectangle(xy(x.toDouble(), y.toDouble()), xy(x + 1.0, y + 1.0), Style.STROKE)
                }
            }*/
            listOf(dd, dh, hd, hh), listOf(
                PWMA_StateSpace.Transition(dd, dh),
                PWMA_StateSpace.Transition(dd, dd),
                PWMA_StateSpace.Transition(hh, hd),
                PWMA_StateSpace.Transition(dd, hd),
                PWMA_StateSpace.Transition(hd, dd),
                PWMA_StateSpace.Transition(hh, dh)
            )
    )*/
}

fun RectangleOdeModel.fixedPoint(input: Set<Int>): Set<Int> {
    var iteration = input
    do {
        val old = iteration
        iteration = iteration + iteration.flatMap { it.successors(false).asSequence().map { it.target }.toList() }.toSet()
    } while (old.toList().sorted() != iteration.toList().sorted())
    return iteration
}

fun RectangleOdeModel.invert(input: Set<Int>): Set<Int> = (0 until stateCount).toSet() - input