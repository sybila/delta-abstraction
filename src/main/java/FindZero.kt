
import java.io.File
import java.util.*

private val singlePrecision = 0.05
private val precision = singlePrecision * singlePrecision
private val timeBound = 2.2

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
(set-logic QF_NRA)
(declare-fun p () Real [0.0, 1.0])
(declare-fun q () Real [0.0, 1.0])
(declare-fun x () Real [-0.1, 10.1])
(declare-fun y () Real [-0.1, 10.1])
(assert (= p 0.011))
(assert (= q 0.1))
(assert (= 0 (- (* ${HillP("y", "0.5")} ${HillN("x", "0.5")}) (* p x))))
(assert (= 0 (- (+ (0.05) (* (0.00016) ${HillN("(* y y)", "16")} ${HillN("x", "5")}) (* (1.6) ${HillP("(* y y)", "16")} ${HillN("x", "5")})) (* q y))))
#commands
(check-sat)
(exit)

"""

fun HillP(x: String, t: String) = "(/ ($x) (+ ($x) ($t)))"
fun HillN(x: String, t: String) = "(/ ($t) (+ ($x) ($t)))"

fun main(args: Array<String>) {

    val start = System.currentTimeMillis()
    val done = ArrayList<Rect>()
    val steady = ArrayList<Rect>()
    val unsafe = ArrayList<Rect>()
    var recompute = listOf(Rect(0.0, 0.0, 10.0, 10.0))

    while (recompute.isNotEmpty()) {
        println("Recompute: ${recompute.size}")
        recompute = recompute.mapIndexed { i, rect -> i to rect }.flatMap { (i, r) ->
            if (r.volume < precision) {
                println("Unsafe.")
                unsafe.add(r)
                emptyList<Rect>()
            } else {
                val flowQuery = modelTemplate.replace("#commands",
                        """
(assert (and (<= x ${r.x2}) (>= x ${r.x1}) (<= y ${r.y2}) (>= y ${r.y1})))
                    """
                )
                println(flowQuery)
                if (isUnsat(flowQuery)) {
                    println("Safe. ${r.volume} $i/${recompute.size}")
                    done.add(r)
                    emptyList<Rect>()
                } else {
                    println("Split. ${r.volume} $i/${recompute.size}")
                    //println("Split $r")
                    r.split()
                }
            }
        }
    }

    val output = File("/Users/daemontus/Downloads/test.svg")
    val multiplier = 100.0
    /*val image = SVG(1000.0, 1000.0) {
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