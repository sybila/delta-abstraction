package dreal

import svg.Point
import svg.Style
import java.util.*

class Rectangle(
        private val bounds: DoubleArray
) {

    val dimensions = bounds.size / 2
    val degenerateDimensions: Int = bounds.mapIntervals { a, b -> if (a == b) 1 else 0 }.sum()

    val volume = bounds.mapIntervals { a, b -> b - a }.fold(1.0) { a, b -> a * b }

    val array
        get() = bounds

    init {
        if (dimensions > 10) error("More than 10 dimensions are currently not supported!")
        if (bounds.size % 2 == 1) error("Bounds array in $this has an odd length.")
        bounds.findInterval { a, b -> a > b }?.let { error("Empty bound $it in $this") }
    }

    fun lBound(dim: Int) = bounds[2 * dim]
    fun hBound(dim: Int) = bounds[2 * dim + 1]

    /**
     * Split this rectangle in every dimension, producing 2^|non-deg. dim| smaller rectangles.
     */
    fun split(): Set<Rectangle> {
        // A list of 2^dimensions binary numbers which correspond to all possible combinations of splits.
        // So for N=2, we get {00, 01, 10, 11}
        val splitPoints = bounds.mapIntervals { a, b -> a + (b-a)/2 }
        return (0 until 1.shl(dimensions)).map { mask ->
            Rectangle(DoubleArray(2*dimensions) { i ->
                val d = i / 2
                if (mask.shr(d) % 2 == 0) {
                    // we want the lower interval in dimension d
                    if (i % 2 == 0) bounds[i] else splitPoints[d]
                } else {
                    // we want the upper interval in dimension d
                    if (i % 2 == 0) splitPoints[d] else bounds[i]
                }
            })
        }.toSet()   // If we have degenerate dimensions, some rectangles will be equivalent.
    }

    /**
     * Remove [dim] dimension, projecting this rectangle.
     */
    fun project(dim: Int): Rectangle = Rectangle(DoubleArray(bounds.size - 2) { i ->
        val d = i / 2
        if (d < dim) bounds[i]
        else bounds[i+2]
    })

    /**
     * If [dimensions] == 2, generate an equivalent svg rectangle.
     */
    fun toSvgRectangle(): svg.Rectangle {
        if (bounds.size != 4) error("Only 2D rectangles can be drawn in SVG.")
        val center = Point((bounds[0] + bounds[1]) / 2, (bounds[2] + bounds[3]) / 2)
        val dimensions = Point(bounds[1] - bounds[0], bounds[3] - bounds[2])
        return svg.Rectangle(center, dimensions, Style.STROKE)
    }

    /** Equality is based on the bounds array **/

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as Rectangle

        if (!Arrays.equals(bounds, other.bounds)) return false

        return true
    }

    override fun hashCode(): Int {
        return Arrays.hashCode(bounds)
    }

    override fun toString(): String {
        return bounds.mapIntervals { a, b -> if (a == b) a.toString() else "[$a, $b]" }
                .joinToString(prefix = "R[", postfix = "]")
    }


}
/*

data class RectangleOld(
        // vector of pairs: [[x_l, x_h], [y_l, y_h], [z_l, z_h], ...]
        // note that some intervals may be singular (one point), but no can be empty
        internal val bounds: DoubleArray
) {

    val dimensions
            get() = bounds.size / 2

    val facets: Sequence<Rectangle>
        get() = (0 until dimensions)
                .asSequence()
                .flatMap {
                    sequenceOf(getFacet(it, true), getFacet(it, false))
                }

    @Transient
    val degenrateDimensions: Int = bounds.mapIntervals { a, b -> if (a == b) 1 else 0 }.sum()

    init {
        if (bounds.size % 2 == 1) error("Bounds array in $this has an odd length.")
        bounds.findInterval { a, b -> a > b }?.let { error("Empty bound $it in $this") }
    }

    @Transient
    val vertices: Sequence<DoubleArray> = buildSequence {
        val result = DoubleArray(bounds.size / 2)
        nextDimension(0, result)
    }

    private suspend fun SequenceBuilder<DoubleArray>.nextDimension(dim: Int, result: DoubleArray) {
        if (dim == dimensions) yield(result)
        else {
            result[dim] = bounds[2 * dim]
            nextDimension(dim + 1, result)
            result[dim] = bounds[2 * dim + 1]
            nextDimension(dim + 1, result)
        }
    }

    fun contains(dim: Int, value: Double): Boolean = value >= bounds[2*dim] && value < bounds[2*dim + 1]

    fun project(dim: Int): Rectangle = Rectangle(DoubleArray(bounds.size - 2) { i ->
        val d = i / 2
        if (d < dim) bounds[i]
        else bounds[i+2]
    })

    fun size(dimension: Int): Double = bounds[2 * dimension + 1] - bounds[2 * dimension]

    fun bound(dimension: Int, high: Boolean): Double = bounds[2 * dimension + if (high) 1 else 0]

    fun split(dimension: Int): Pair<Rectangle, Rectangle> {
        val splitPoint = (bounds[2*dimension] + bounds[2*dimension + 1]) / 2
        val low = Rectangle(DoubleArray(bounds.size) { i ->
            val d = i / 2
            if (d == dimension && i % 2 == 1) splitPoint else bounds[i]
        })
        val high = Rectangle(DoubleArray(bounds.size) { i ->
            val d = i / 2
            if (d == dimension && i % 2 == 0) splitPoint else bounds[i]
        })
        return low to high
    }

    fun intersect(other: Rectangle): Rectangle? {
        val newBounds = DoubleArray(bounds.size) {
            if (it % 2 == 0) Math.max(bounds[it], other.bounds[it])
            else Math.min(bounds[it], other.bounds[it])
        }
        val isValid = newBounds.indices.filter { it % 2 == 0 }.any { bounds[it] > bounds[it+1] }
        return if (isValid) null else Rectangle(newBounds)
    }

    fun weave(): List<Rectangle> {
        if (bounds.size != 4) error("Currently, we weave only on 2D rectangles :P")
        val sizeX = bounds[1] - bounds[0]
        val sizeY = bounds[3] - bounds[2]
        val splitX1 = bounds[0] + (1.0/3.0) * sizeX
        val splitX2 = bounds[0] + (2.0/3.0) * sizeX
        val splitY1 = bounds[2] + (1.0/3.0) * sizeY
        val splitY2 = bounds[2] + (2.0/3.0) * sizeY

        return listOf(
                Rectangle(doubleArrayOf(bounds[0], splitX1, bounds[2], splitY2)),   // left, down
                Rectangle(doubleArrayOf(bounds[0], splitX2, splitY2, bounds[3])),   // left, up
                Rectangle(doubleArrayOf(splitX2, bounds[1], splitY1, bounds[3])),   // right, up
                Rectangle(doubleArrayOf(splitX1, bounds[1], bounds[2], splitY1)),   // right, down
                Rectangle(doubleArrayOf(splitX1, splitX2, splitY1, splitY2))        // center
        )
    }

    fun getFacet(dimension: Int, positive: Boolean): Rectangle
            = Rectangle(DoubleArray(bounds.size) { i ->
        val d = i / 2
        if (d != dimension) bounds[i]
        else {
            val bound = if (positive) 1 else 0
            bounds[2 * d + bound]
        }
    })

    // return null if intersection has less than n-1 dimensions
    fun getFacetIntersection(other: Rectangle): FacetIntersection? {
        if (this.bounds.size != other.bounds.size) error("Rectangles not compatible")
        val intersection = DoubleArray(bounds.size) { i ->
            if (i % 2 == 0) {
                maxOf(this.bounds[i], other.bounds[i])
            } else {
                minOf(this.bounds[i], other.bounds[i])
            }
        }
        if (intersection.findInterval { a, b -> a > b } != null) return null    // empty intersection
        val degeneracy = intersection.mapIntervals { a, b -> if (a == b) 1 else 0 }
        val degenerateDimensions = degeneracy.sum()
        return when {
            degenerateDimensions == 0 -> error("Rectangles $this and $other have non-degenerate intersection!")
            degenerateDimensions > 1 -> {
                null
            }
            else -> {
                val dimension = degeneracy.indexOfFirst { it == 1 }
                val positive = this.bounds[2*dimension+1] == other.bounds[2*dimension]
                FacetIntersection(Rectangle(intersection), dimension, positive)
            }
        }
    }

    /**
     * Contains - intersection rectangle, dimension on which the facets intersect, true if the target rectangle
     * is higher than the argument rectangle in that dimension (positive trajectory flow)
     */
    data class FacetIntersection(
            val rectangle: Rectangle, val dimension: Int, val positive: Boolean
    )

    fun toSvgRectangle(): svg.Rectangle {
        if (bounds.size != 4) error("Only 2D rectangles can be drawn in SVG.")
        val center = Point((bounds[0] + bounds[1]) / 2, (bounds[2] + bounds[3]) / 2)
        val dimensions = Point(bounds[1] - bounds[0], bounds[3] - bounds[2])
        return svg.Rectangle(center, dimensions, Style.STROKE)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as Rectangle

        if (!Arrays.equals(bounds, other.bounds)) return false

        return true
    }

    override fun hashCode(): Int {
        return Arrays.hashCode(bounds)
    }

    override fun toString(): String {
        return bounds.mapIntervals { a, b -> if (a == b) a.toString() else "[$a, $b]" }
                .joinToString(prefix = "R[", postfix = "]")
    }

}*/