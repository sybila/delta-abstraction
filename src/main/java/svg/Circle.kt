package svg

data class Circle(
        override val center: Point,
        val radius: Double,
        override val style: Style
) : SvgPrimitive<Circle> {

    override val anchors: Sequence<Point>
        get() = sequenceOf(left, up, right, down)

    val up: Point
        get() = center + Point(0.0, radius)

    val down: Point
        get() = center + Point(0.0, -radius)

    val left: Point
        get() = center + Point(-radius, 0.0)

    val right: Point
        get() = center + Point(radius, 0.0)

    fun anchor(d: Dimension, positive: Boolean): Point = when {
        d == Dimension.X && positive -> right
        d == Dimension.X && !positive -> left
        d == Dimension.Y && positive -> up
        else -> down
    }

    override fun compileSvg(): String =
            """<circle cx="${center.x}" cy="${center.y}" r="$radius" ${style.compileAttributes()} />"""

    override fun scale(factor: Double): Circle =
            copy(center = center * factor, radius = radius * factor)

    override fun flipY(height: Double): Circle =
            copy(center = center.flipY(height))

    override fun translate(delta: Point): Circle =
            copy(center = center + delta)
}