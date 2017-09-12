import java.util.*

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