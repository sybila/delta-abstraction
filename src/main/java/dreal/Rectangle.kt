package dreal

import svg.Point
import svg.Style
import java.util.*
import kotlin.coroutines.experimental.SequenceBuilder
import kotlin.coroutines.experimental.buildSequence

data class Rectangle(
        // vector of pairs: [[x_l, x_h], [y_l, y_h], [z_l, z_h], ...]
        // note that some intervals may be singular (one point), but no can be empty
        private val bounds: DoubleArray
) {

    @Transient
    val dimensions = bounds.size / 2

    @Transient  // just a public getter
    val intervals = bounds

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
}