
import java.io.File
import java.util.*

private val singlePrecision = 0.1
private val precision = singlePrecision * singlePrecision
private val timeBound = 1.1

data class Rect(val x1: Double, val y1: Double, val x2: Double, val y2: Double) {

    init {
        if (x2 <= x1 || y2 <= y1) error("Negative size rectangle $this")
    }

    val width: Double = Math.abs(x2 - x1)
    val height: Double = Math.abs(y2 - y1)

    val volume: Double = width * height

    fun split(): List<Rect> {
        val mX = x1 + (width / 2)
        val mY = y1 + (height / 2)
        //println("Splitting $this")
        return listOf(
                Rect(x1, y1, mX, mY),
                Rect(x1, mY, mX, y2),
                Rect(mX, y1, x2, mY),
                Rect(mX, mY, x2, y2)
        )
    }

}

private fun isUnsat(query: String): Boolean {
    val s = System.currentTimeMillis()
    val tempFile = File.createTempFile("input", ".smt2")
    tempFile.writeText(query)
    val process = Runtime.getRuntime().exec(arrayOf("/usr/local/bin/dreal", tempFile.absolutePath))
    val output = process.inputStream.bufferedReader().readLines()
    //println("Result ${output} ${output == listOf("unsat")}")
    //println("Solve time ${System.currentTimeMillis() - s}")
    return output == listOf("unsat")
}

private val modelTemplate =
"""
(set-logic QF_NRA_ODE)
(declare-fun p () Real [0.9, 1.1])
(declare-fun x () Real [-0.1, 4.1])
(declare-fun y () Real [-0.1, 4.1])
(declare-fun x_z () Real [-0.1, 4.1])
(declare-fun y_z () Real [-0.1, 4.1])
(declare-fun x_0_0 () Real [-0.1, 4.1])
(declare-fun y_0_0 () Real [-0.1, 4.1])
(declare-fun p_0_0 () Real [0.9, 1.1])
(declare-fun x_0_t () Real [-0.1, 4.1])
(declare-fun y_0_t () Real [-0.1, 4.1])
(declare-fun p_0_t () Real [0.9, 1.1])
(declare-fun time_0 () Real [0.0, $timeBound])
(define-ode flow_1 ((= d/dt[x] (- y x)) (= d/dt[p] (0)) (= d/dt[y] (- 2 (* p y)))))
(assert (= [x_0_t p_0_t y_0_t] (integral 0. time_0 [x_0_0 p_0_0 y_0_0] flow_1)))
(assert (= time_0 $timeBound))
(assert (= (- y_z x_z) 0))
(assert (= (- 2 (* p y_z)) 0))
#commands
(check-sat)
(exit)
"""

fun main(args: Array<String>) {

    val start = System.currentTimeMillis()
    val done = ArrayList<Rect>()
    val steady = ArrayList<Rect>()
    val unsafe = ArrayList<Rect>()
    var recompute = listOf(Rect(0.0, 0.0, 4.0, 4.0))

    while (recompute.isNotEmpty()) {
        println("Recompute: ${recompute.size}")
        recompute = recompute.flatMap { r ->
            val flowQuery = modelTemplate.replace("#commands",
                    """
(assert (forall_t 1 [0 time_0] (and (< x_0_t ${r.x2}) (> x_0_t ${r.x1}) (< y_0_t ${r.y2}) (> y_0_t ${r.y1}))))
(assert (and (< x_0_0 ${r.x2}) (> x_0_0 ${r.x1}) (< y_0_0 ${r.y2}) (> y_0_0 ${r.y1})))
(assert (and (<= x_0_t ${r.x2}) (>= x_0_t ${r.x1}) (<= y_0_t ${r.y2}) (>= y_0_t ${r.y1})))
                    """
            )
            if (r.volume < precision) {
                if (isUnsat(flowQuery)) {
                    done.add(r)
                } else {
                    println("Unsafe.")
                    unsafe.add(r)
                    println(flowQuery)
                }
                emptyList<Rect>()
            } else {
                val steadyQuery = modelTemplate.replace("#commands",
                        """
(assert (forall_t 1 [0 time_0] (and (< x_0_t ${r.x2}) (> x_0_t ${r.x1}) (< y_0_t ${r.y2}) (> y_0_t ${r.y1}))))
(assert (and (< x_0_0 ${r.x2}) (> x_0_0 ${r.x1}) (< y_0_0 ${r.y2}) (> y_0_0 ${r.y1})))
(assert (and (<= x_0_t ${r.x2}) (>= x_0_t ${r.x1}) (<= y_0_t ${r.y2}) (>= y_0_t ${r.y1})))
(assert (and (or (> (- x_0_t x_z) $singlePrecision) (< (- x_0_t x_z) -$singlePrecision)) (or (> (- y_0_t y_z) $singlePrecision) (< (- y_0_t y_z) -$singlePrecision))))
                            """)
                if (isUnsat(flowQuery)) {
                    println("Safe. ${r.volume}")
                    done.add(r)
                    emptyList<Rect>()
                } else if (isUnsat(steadyQuery)) {
                    println("Steady. ${r.volume}")
                    steady.add(r)
                    emptyList<Rect>()
                } else {
                    println("Split. ${r.volume}")
                    //println("Split $r")
                    r.split()
                }
            }
        }
    }

    val output = File("/Users/daemontus/Downloads/test.svg")
    val multiplier = 100.0
    /*val image = SVG(400.0, 400.0) {
        done.forEach {
            addRectangle(it.x1 * multiplier, it.y1 * multiplier, it.x2 * multiplier, it.y2 * multiplier, fill = 0.0)
        }
        steady.forEach {
            addRectangle(it.x1 * multiplier, it.y1 * multiplier, it.x2 * multiplier, it.y2 * multiplier, fill = 0.0)
        }
        unsafe.forEach {
            addRectangle(it.x1 * multiplier, it.y1 * multiplier, it.x2 * multiplier, it.y2 * multiplier, fill = 1.0)
        }
    }*/
    /*println("Unsafe: ${unsafe.first()}")
    unsafe.forEach {  r ->
        val flowQuery = modelTemplate.replace("#commands",
                """
(assert (forall_t 1 [0 time_0] (and (< x_0_t ${r.x2}) (> x_0_t ${r.x1}) (< y_0_t ${r.y2}) (> y_0_t ${r.y1}))))
(assert (and (< x_0_0 ${r.x2}) (> x_0_0 ${r.x1}) (< y_0_0 ${r.y2}) (> y_0_0 ${r.y1})))
(assert (and (<= x_0_t ${r.x2}) (>= x_0_t ${r.x1}) (<= y_0_t ${r.y2}) (>= y_0_t ${r.y1})))
                    """
        )
        val steadyQuery = modelTemplate.replace("#commands",
                """
(assert (forall_t 1 [0 time_0] (and (< x_0_t ${r.x2}) (> x_0_t ${r.x1}) (< y_0_t ${r.y2}) (> y_0_t ${r.y1}))))
(assert (and (< x_0_0 ${r.x2}) (> x_0_0 ${r.x1}) (< y_0_0 ${r.y2}) (> y_0_0 ${r.y1})))
(assert (and (<= x_0_t ${r.x2}) (>= x_0_t ${r.x1}) (<= y_0_t ${r.y2}) (>= y_0_t ${r.y1})))
(assert (and (or (> (- x_0_t x_z) $singlePrecision) (< (- x_0_t x_z) -$singlePrecision)) (or (> (- y_0_t y_z) $singlePrecision) (< (- y_0_t y_z) -$singlePrecision))))
                            """)
        println("${isUnsat(flowQuery)}, ${isUnsat(steadyQuery)}")
        if (!isUnsat(flowQuery)) {
            println(steadyQuery)
            return
        }
    }*/
    //println("Elapsed: ${System.currentTimeMillis() - start}")
    //output.writeText(image)
}