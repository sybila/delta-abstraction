package svg
/**
 * Interface for objects drawable into an SVG vector file.
 */
interface SvgPrimitive<P : SvgPrimitive<P>> {

    /**
     * svg.Style properties of this primitive.
     */
    val style: Style

    /**
     * Geometrically central point of this structure.
     */
    val center: Point

    /**
     * Iterate over anchors of this primitive.
     * The whole primitive should be visible inside a rectangle which fits all anchors.
     */
    val anchors: Sequence<Point>

    /**
     * Compile this primitive into a set of svg elements which can directly used within the result file.
     */
    fun compileSvg(): String

    /**
     * Resize this object using [0,0] as the center of resizing.
     */
    fun scale(factor: Double): P

    /**
     * Move this object by [delta].
     */
    fun translate(delta: Point): P

    /**
     * Flip the object with respect to the given height.
     * This is useful for inverting the Y axis to resemble scientific coordinate systems.
     */
    fun flipY(height: Double): P

}