package dreal

import java.io.File

fun checkNotSat(query: String, precision: Double = 0.001): Boolean {
    val tempFile = File.createTempFile("input", ".smt2")
    tempFile.writeText(query)
    val process = Runtime.getRuntime().exec(arrayOf(
            "/usr/local/bin/dreal", "--precision", precision.toString(), tempFile.absolutePath))
    val output = process.inputStream.bufferedReader().readLines()
    return when {
        output.last() == "unsat" -> true
        "delta-sat" !in output.last() -> error("Solver failed: $output")
        else -> false
    }
}

data class Rect(val x1: Double, val y1: Double, val x2: Double, val y2: Double) {

    init {
        if (x2 <= x1 || y2 <= y1) error("Negative size rectangle $this")
    }

    constructor(x: Pair<Double, Double>, y: Pair<Double, Double>): this(x.first, y.first, x.second, y.second)

    val width: Double = Math.abs(x2 - x1)
    val height: Double = Math.abs(y2 - y1)

    val volume: Double = width * height

    fun split(): List<Rect> {
        val mX = x1 + (width / 2)
        val mY = y1 + (height / 2)
        return listOf(
                Rect(x1, y1, mX, mY),
                Rect(x1, mY, mX, y2),
                Rect(mX, y1, x2, mY),
                Rect(mX, mY, x2, y2)
        )
    }

    fun boundsQuery(x: String, y: String) = "(assert (and (<= $x $x2) (>= $x $x1) (<= $y $y2) (>= $y $y1)))"

}

fun makeQuery(query: String) =
"""
(set-logic QF_NRA_ODE)
$query
(check-sat)
(exit)
""".trim()

sealed class State {

    /**
     * Abstract state representing the trajectories outside of the system bounds.
     */
    object Exterior : State()

    /**
     * Abstract state representing the interior trajectories of given [rectangle].
     */
    data class Interior(val rectangle: Rectangle) : State()

    /**
     * Abstract state representing trajectories flowing [from] one given rectangle [to] the other one.
     */
    data class Transition(val from: Rectangle?, val to: Rectangle?) : State()

}