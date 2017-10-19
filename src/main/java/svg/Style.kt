package svg

/**
 * A universal style object for any [SvgPrimitive]. Later, we might want to create specific styles
 * for different objects, but this is ok for now.
 */
data class Style(private val properties: Map<String, String>) {
    companion object {
        val DEFAULT = Style(emptyMap())
        val STROKE = Style(mapOf("stroke-width" to "1", "stroke" to "black", "fill" to "transparent"))
        val FILL = Style(mapOf("fill" to "black"))
        val ARROW = Style(mapOf("marker-end" to "url(#arrow)", "stroke-width" to "1", "stroke" to "black"))
    }

    fun compileAttributes(): String = buildString {
        for ((key, value) in properties) {
            append("$key=\"$value\" ")
        }
    }

    fun strokeWidth(width: Double) = copy(properties + ("stroke-width" to width.toString()))

    fun storkeColor(color: String) = copy(properties + ("storke" to color))

    fun fillColor(color: String) = copy(properties + ("fill" to color))

    fun markerEnd(url: String) = copy(properties + ("marker-end" to url))
}