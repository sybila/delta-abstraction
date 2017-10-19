package svg

data class Line(
        val begin: Point,
        val end: Point,
        override val style: Style = Style.STROKE
) : SvgPrimitive<Line> {

    override val anchors: Sequence<Point>
        get() = sequenceOf(begin, end)

    override val center: Point
        get() = (begin + end) * 0.5

    override fun compileSvg(): String {
        val (x1, y1) = begin
        val (x2, y2) = end
        return """<line x1="$x1" y1="$y1" x2="$x2" y2="$y2" ${style.compileAttributes()}/>"""
    }

    override fun scale(factor: Double): Line = copy(begin = begin * factor, end = end * factor)

    override fun translate(delta: Point): Line = copy(begin = begin + delta, end = end + delta)

    override fun flipY(height: Double): Line = copy(begin = begin.flipY(height), end = end.flipY(height))
}