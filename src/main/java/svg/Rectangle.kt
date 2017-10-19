package svg

data class Rectangle(
        override val center: Point,
        val dimensions: Point,
        override val style: Style
) : SvgPrimitive<Rectangle> {

    override val anchors: Sequence<Point>
        get() = sequenceOf(leftDown, leftUp, rightUp, rightDown)

    val leftDown: Point
        get() = center + (dimensions * -0.5)

    val rightUp: Point
        get() = center + (dimensions * 0.5)

    val leftUp: Point
        get() = center + (xy(dimensions.x * -0.5, dimensions.y * 0.5))

    val rightDown: Point
        get() = center + (xy(dimensions.x * 0.5, dimensions.y * -0.5))

    val width: Double
        get() = dimensions.x

    val height: Double
        get() = dimensions.y

    override fun compileSvg(): String {
        val (x, y) = center + (dimensions * -0.5)
        val (width, height) = dimensions
        return """<rect x="$x" y="$y" width="$width" height="$height" ${style.compileAttributes()}/>"""
    }

    override fun scale(factor: Double): Rectangle = copy(center = center * factor, dimensions = dimensions * factor)

    override fun translate(delta: Point): Rectangle = copy(center = center + delta)

    override fun flipY(height: Double): Rectangle = copy(center = center.flipY(height))
}