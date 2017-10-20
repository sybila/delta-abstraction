package svg

/**
 * Point in 2D space. We assume a 2D standard vector space with addition and multiplication by scalar.
 */
data class Point(val x: Double, val y: Double) : Comparable<Point> {

    companion object {
        val ZERO = Point(0.0, 0.0)
    }

    operator fun plus(other: Point) = Point(x + other.x, y + other.y)

    operator fun minus(other: Point) = Point(x - other.x, y - other.y)

    operator fun times(num: Double) = Point(x * num, y * num)

    fun flipY(height: Double) = Point(x, height - y)

    fun distanceTo(other: Point): Double {
        val dX = Math.abs(other.x - this.x)
        val dY = Math.abs(other.y - this.y)
        return Math.sqrt(dX * dX + dY * dY)
    }

    override fun compareTo(other: Point): Int = if (x == other.x) y.compareTo(other.y) else x.compareTo(other.x)
}