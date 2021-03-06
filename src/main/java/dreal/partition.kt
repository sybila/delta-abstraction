package dreal

import kotlinx.coroutines.experimental.async
import kotlinx.coroutines.experimental.newFixedThreadPoolContext
import java.io.File
import java.util.*
import java.util.concurrent.atomic.AtomicInteger
import kotlin.collections.ArrayList
/*
val pool = newFixedThreadPoolContext(4, "foo")

suspend fun ModelFactory.makePartitions(precision: Double = 0.001, timeBound: Double = 1.0) {
    val volumeThreshold = 0.01
    val solver = Grid1Solver(dimensionBounds(2))

    //val (noZero, zero) = splitByZero(volumeThreshold, precision)
    val (flow, noFlow) = splitByFlow(listOf(Rect(dimensionBounds(0), dimensionBounds(1))), volumeThreshold, precision, timeBound)

    val safe = flow
    val unsafe = noFlow
    //val unsafe = splitByParam(noFlow, solver, volumeThreshold, precision, timeBound)

    val c = AtomicInteger(0)
    val probablyUnsafe = ArrayList<Rect>()
    println("Unsafe: ${unsafe.size}")
    unsafe.map { r -> async(pool) {
        c.incrementAndGet().takeIf { it % 100 == 0 }?.let { println(it) }
        val admissibleXUp = makeQuery(
                """
                        ${makeHead()}
                        ${r.boundsQuery(x, y)}
                        (assert (= x ${r.x2}))
                        (assert (>= 0 ${makeModelEquation(0)}))
                    """
        )
        val slowFlowXUp = makeQuery(
                """
                        ${makeHead()}
                        ${makeHead("_0_0")}
                        ${makeHead("_0_t")}
                        (declare-fun time () Real [0.0, $timeBound])
                        ${makeFlow()}
                        (assert (= time $timeBound))
                        (assert (= [x_0_t y_0_t p_0_t] (integral 0. time [x_0_0 y_0_0 p_0_0] flow_1)))
                        ${r.boundsQuery("x_0_0", "y_0_0")}
                        ${r.boundsQuery("x_0_t", "y_0_t")}
                        (assert (= x_0_0 ${r.x2}))
                        (assert (forall_t 1 [0 time] (and (< x_0_t ${r.x2}) (> x_0_t ${r.x1}) (< y_0_t ${r.y2}) (> y_0_t ${r.y1}))))
                    """
        )
        val admissibleXDown = makeQuery(
                """
                        ${makeHead()}
                        ${r.boundsQuery(x, y)}
                        (assert (= x ${r.x1}))
                        (assert (<= 0 ${makeModelEquation(0)}))
                    """
        )
        val slowFlowXDown = makeQuery(
                """
                        ${makeHead()}
                        ${makeHead("_0_0")}
                        ${makeHead("_0_t")}
                        (declare-fun time () Real [0.0, $timeBound])
                        ${makeFlow()}
                        (assert (= time $timeBound))
                        (assert (= [x_0_t y_0_t p_0_t] (integral 0. time [x_0_0 y_0_0 p_0_0] flow_1)))
                        ${r.boundsQuery("x_0_0", "y_0_0")}
                        ${r.boundsQuery("x_0_t", "y_0_t")}
                        (assert (= x_0_0 ${r.x1}))
                        (assert (forall_t 1 [0 time] (and (< x_0_t ${r.x2}) (> x_0_t ${r.x1}) (< y_0_t ${r.y2}) (> y_0_t ${r.y1}))))
                    """
        )
        val admissibleYUp = makeQuery(
                """
                        ${makeHead()}
                        ${r.boundsQuery(x, y)}
                        (assert (= y ${r.y2}))
                        (assert (>= 0 ${makeModelEquation(1)}))
                    """
        )
        val slowFlowYUp = makeQuery(
                """
                        ${makeHead()}
                        ${makeHead("_0_0")}
                        ${makeHead("_0_t")}
                        (declare-fun time () Real [0.0, $timeBound])
                        ${makeFlow()}
                        (assert (= time $timeBound))
                        (assert (= [x_0_t y_0_t p_0_t] (integral 0. time [x_0_0 y_0_0 p_0_0] flow_1)))
                        ${r.boundsQuery("x_0_0", "y_0_0")}
                        ${r.boundsQuery("x_0_t", "y_0_t")}
                        (assert (= y_0_0 ${r.y2}))
                        (assert (forall_t 1 [0 time] (and (< x_0_t ${r.x2}) (> x_0_t ${r.x1}) (< y_0_t ${r.y2}) (> y_0_t ${r.y1}))))
                    """
        )
        val admissibleYDown = makeQuery(
                """
                        ${makeHead()}
                        ${r.boundsQuery(x, y)}
                        (assert (= y ${r.y1}))
                        (assert (<= 0 ${makeModelEquation(1)}))
                    """
        )
        val slowFlowYDown = makeQuery(
                """
                        ${makeHead()}
                        ${makeHead("_0_0")}
                        ${makeHead("_0_t")}
                        (declare-fun time () Real [0.0, $timeBound])
                        ${makeFlow()}
                        (assert (= time $timeBound))
                        (assert (= [x_0_t y_0_t p_0_t] (integral 0. time [x_0_0 y_0_0 p_0_0] flow_1)))
                        ${r.boundsQuery("x_0_0", "y_0_0")}
                        ${r.boundsQuery("x_0_t", "y_0_t")}
                        (assert (= y_0_0 ${r.y1}))
                        (assert (forall_t 1 [0 time] (and (< x_0_t ${r.x2}) (> x_0_t ${r.x1}) (< y_0_t ${r.y2}) (> y_0_t ${r.y1}))))
                    """
        )
        val safeXUp = !checkNotSat(admissibleXUp) && checkNotSat(slowFlowXUp)
        val safeXDown = !checkNotSat(admissibleXDown) && checkNotSat(slowFlowXDown)
        val safeYUp = !checkNotSat(admissibleYUp) && checkNotSat(slowFlowYUp)
        val safeYDown = !checkNotSat(admissibleYDown) && checkNotSat(slowFlowYDown)
        val someSafe = safeXUp || safeXDown || safeYUp || safeYDown
        //val someSafe = checkNotSat(slowFlowXUp, precision) || checkNotSat(slowFlowXDown, precision) || checkNotSat(slowFlowYDown, precision) || checkNotSat(slowFlowYUp, precision)
        if (someSafe) synchronized(probablyUnsafe) { probablyUnsafe.add(r) }
    } }.forEach { it.await() }

    val output = File("/Users/daemontus/Downloads/test.svg")
    val multiplier = 100.0
    val shift = 0.0//400.0
    /*val image = SVG(1000.0, 1000.0) {
        safe.forEach {
            addRectangle(it.x1 * multiplier + shift, it.y1 * multiplier + shift, it.x2 * multiplier + shift, it.y2 * multiplier + shift, fill = 0.0)
        }
        probablyUnsafe.forEach {
            addRectangle(it.x1 * multiplier + shift, it.y1 * multiplier + shift, it.x2 * multiplier + shift, it.y2 * multiplier + shift, fill = 1.0)
        }
        /*unsafe.forEach { (it, p) ->
            addRectangle(it.x1 * multiplier, it.y1 * multiplier, it.x2 * multiplier, it.y2 * multiplier, fill = (p?.cardinality ?: 0.0) / solver.TT.cardinality)
        }*/
    }*/

    /*unsafe.forEach { t, u ->
        /*if (t.y1 > 0.0) {
        }*/
        println("$t: $u (${(u?.cardinality ?: 0.0) / solver.TT.cardinality})")
    }*/

    //output.writeText(image)
}

suspend fun ModelFactory.splitByZero(volumeThreshold: Double, precision: Double): Pair<List<Rect>, List<Rect>> {
    val zero = ArrayList<Rect>()
    val noZero = ArrayList<Rect>()
    var recompute = listOf(Rect(dimensionBounds(0), dimensionBounds(1)))
    do {
        println("Recompute: ${recompute.size}")
        recompute = recompute.map { r -> async(pool) {
            if (r.volume < volumeThreshold) {
                synchronized(zero) { zero.add(r) }
                emptyList()
            } else {
                val hasZero = makeQuery(
                        """
                        ${makeHead()}
                        ${makeEqulibrium()}
                        ${r.boundsQuery(x, y)}
                        """
                )
                if (checkNotSat(hasZero, precision)) {
                    synchronized(noZero) { noZero.add(r) }
                    emptyList()
                } else {
                    r.split()
                }
            }
        } }.flatMap { it.await() }
    } while (recompute.isNotEmpty())
    return noZero to zero
}

suspend fun ModelFactory.splitByFlow(init: List<Rect>, volumeThreshold: Double, precision: Double, timeBound: Double): Pair<List<Rect>, List<Rect>> {
    val flow = ArrayList<Rect>()
    val noFlow = ArrayList<Rect>()
    var recompute = init
    // confirm zeroes
    do {
        println("Non zero: ${recompute.size}")
        recompute = recompute.map { r -> async(pool) {
            val slowFlow = makeQuery(
                    """
                        ${makeHead()}
                        ${makeHead("_0_0")}
                        ${makeHead("_0_t")}
                        (declare-fun time () Real [0.0, $timeBound])
                        ${makeFlow()}
                        (assert (= time $timeBound))
                        (assert (= [x_0_t y_0_t p_0_t] (integral 0. time [x_0_0 y_0_0 p_0_0] flow_1)))
                        ${r.boundsQuery("x_0_0", "y_0_0")}
                        ${r.boundsQuery("x_0_t", "y_0_t")}
                        (assert (forall_t 1 [0 time] (and (< x_0_t ${r.x2}) (> x_0_t ${r.x1}) (< y_0_t ${r.y2}) (> y_0_t ${r.y1}))))
                    """
            )
            //println(slowFlow)
            if (checkNotSat(slowFlow, precision)) {
                synchronized(flow) { flow.add(r) }
                emptyList()
            } else {
                if (r.volume < volumeThreshold) {
                    synchronized(noFlow) { noFlow.add(r) }
                    emptyList()
                } else {
                    r.split()
                }
            }
        } }.flatMap { it.await() }
    } while (recompute.isNotEmpty())
    return flow to noFlow
}

suspend fun ModelFactory.splitByParam(init: List<Rect>, solver: Grid1Solver, volumeThreshold: Double, precision: Double, timeBound: Double): Map<Rect, Grid1?> {
    val unsafe = HashMap<Rect, Grid1?>()
    println("Init: ${init.size}")
    var recompute = init.map { it to dimensionBounds(2) }
    while (recompute.isNotEmpty()) {
        println("Param: ${recompute.size}")
        recompute = recompute.map { (r, bound) -> async(pool) {
            val (l, h) = bound
            val slowFlow = makeQuery(
                    """
                        ${makeHead()}
                        ${makeHead("_0_0")}
                        ${makeHead("_0_t")}
                        (declare-fun time () Real [0.0, $timeBound])
                        ${makeFlow()}
                        (assert (= time $timeBound))
                        (assert (= [x_0_t y_0_t p_0_t] (integral 0. time [x_0_0 y_0_0 p_0_0] flow_1)))
                        ${r.boundsQuery(x, y)}
                        ${r.boundsQuery("x_0_0", "y_0_0")}
                        ${r.boundsQuery("x_0_t", "y_0_t")}
                        (assert (forall_t 1 [0 time] (and (< x_0_t ${r.x2}) (> x_0_t ${r.x1}) (< y_0_t ${r.y2}) (> y_0_t ${r.y1}))))
                        (assert (and (<= p $h) (>= p $l)))
                        (assert (and (<= p_0_0 $h) (>= p_0_0 $l)))
                        (assert (and (<= p_0_t $h) (>= p_0_t $l)))
                    """
            )
            if (checkNotSat(slowFlow, precision)) {
                // Ok, do nothing
                println("Safe! ${bound}")
                println(slowFlow)
                emptyList()
            } else {
                if (h - l < volumeThreshold) {
                    val i = Grid1(doubleArrayOf(l, h), BitSet(1).apply { set(0) })
                    synchronized(unsafe) {
                        unsafe[r] = solver.run { unsafe[r] or i }
                    }
                    emptyList()
                } else {
                    val mid = l + (h - l) / 2
                    listOf(r to (l to mid), r to (mid to h))
                }
            }
        } }.flatMap { it.await() }
    }
    println("R: ${unsafe.keys.size}")
    return unsafe
}*/