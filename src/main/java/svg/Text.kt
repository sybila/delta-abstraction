package svg

data class Text(
        val value: String,
        val anchor: Point,
        override val style: Style = Style.FILL
) : SvgPrimitive<Text> {

    override val center: Point = anchor
    override val anchors: Sequence<Point> = sequenceOf(anchor)

    override fun compileSvg(): String = """<text x="${anchor.x}" y="${anchor.y}" font-size="5" ${style.compileAttributes()}>$value</text>"""

    override fun scale(factor: Double): Text = this.copy(anchor = anchor * factor)

    override fun translate(delta: Point): Text = this.copy(anchor = anchor + delta)

    override fun flipY(height: Double): Text = this.copy(anchor = anchor.flipY(height))
}