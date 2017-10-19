
import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.Parser
import svg.PwmaImage
import java.io.File
/*
fun middle(a: Point, b: Point) = Point((a.x + b.x) / 2.0, (a.y + b.y) / 2.0)

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
                from.getEdge(X, true) == to.getEdge(X, false) -> Line(
                        from.toState().anchor(X, true),
                        to.toState().anchor(X, false), Style.STROKE
                )
                from.getEdge(X, false) == to.getEdge(X, true) -> Line(
                        from.toState().anchor(X, false),
                        to.toState().anchor(X, true), Style.STROKE
                )
                from.getEdge(Y, true) == to.getEdge(Y, false) -> Line(
                        from.toState().anchor(Y, false),
                        to.toState().anchor(Y, true), Style.STROKE
                )
                from.getEdge(Y, false) == to.getEdge(Y, true) -> Line(
                        from.toState().anchor(Y, true),
                        to.toState().anchor(Y, false), Style.STROKE
                )
                else -> null
            }
        }.filterNotNull()

        states.forEach {
            appendln(it.compileSvg())
        }

        transitions.forEach {
            it.writeSVG(this)
        }

        highlight.forEach {
            it.map { it + shift }.flipY(height).map { it * scaleFactor }.copy(style = Style.FILL).writeSVG(this)
        }

        appendln("</svg>")
    }

}*/

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
    val thresholds = (0..40).map { it / 4.0 }
    val model = Parser().parse(input).let { m ->
        m.copy(variables = m.variables.map { v ->
            v.copy(thresholds = thresholds)
        })
    }

    val ts = RectangleOdeModel(model, createSelfLoops = true)
    ts.run {
        val stable = (0 until stateCount).filter {
            println("Check stable $it")
            it in invert(backwards(invert(backwards(setOf(it)))))
        }.toSet()
        val c1: Int = stable.first()
        val c2: Int = stable.first { c1 !in backwards(setOf(it)) }
        val r1 = backwards(setOf(c1))
        val r2 = backwards(setOf(c2))
        val and = r1 - (r1 - r2)
        f.bufferedWriter().use { writer ->
            PwmaImage(model, ts, mapOf(
                    "#ff0000" to stable,
                    "#00ff00" to r1,
                    "#0000ff" to r2,
                    "#00ffff" to and
                    )).toSvgImage().normalize(1000.0).writeTo(writer)
        }
    }
}

fun RectangleOdeModel.backwards(input: Set<Int>): Set<Int> {
    var iteration = input
    do {
        val old = iteration
        iteration += iteration.flatMap { it.successors(false).asSequence().map { it.target }.toList() }.toSet()
    } while (old.toList().sorted() != iteration.toList().sorted())
    return iteration
}

fun RectangleOdeModel.invert(input: Set<Int>): Set<Int> = (0 until stateCount).toSet() - input