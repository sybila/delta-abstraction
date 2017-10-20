package svg

data class Rectangle(
        override val center: Point,
        val dimensions: Point,
        override val style: Style
) : SvgPrimitive<Rectangle> {

    override val anchors: Sequence<Point>
        get() = sequenceOf(leftDown, left, leftUp, up, rightUp, right, rightDown, down)

    val secondaryAnchors: Sequence<Point>
        get() = sequenceOf(leftDown to leftUp, leftUp to rightUp, rightUp to rightDown, rightDown to leftDown).flatMap { (a, b) ->
            sequenceOf((a + (b - a) * 0.3), a + (b - a) * 0.7)
        }

    val sizes: Sequence<Double>
        get() = sequenceOf(width, height)

    val leftDown: Point
        get() = center + (dimensions * -0.5)

    val rightUp: Point
        get() = center + (dimensions * 0.5)

    val leftUp: Point
        get() = center + (xy(dimensions.x * -0.5, dimensions.y * 0.5))

    val rightDown: Point
        get() = center + (xy(dimensions.x * 0.5, dimensions.y * -0.5))

    val up: Point
        get() = center + xy(0.0, width * 0.5)

    val down: Point
        get() = center + xy(0.0, width * -0.5)

    val left: Point
        get() = center + xy(height * -0.5, 0.0)

    val right: Point
        get() = center + xy(height * 0.5, 0.0)

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