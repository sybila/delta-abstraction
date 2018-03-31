package dreal

import kotlinx.coroutines.experimental.async
import java.io.File
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicLong

class Timeout : RuntimeException()

val timeouts = AtomicInteger(0)

fun provedUnsat(query: String, precision: Double = 0.001): Boolean {
    val tempFile = File.createTempFile("input", ".smt2")
    tempFile.writeText(query)
    val process = Runtime.getRuntime().exec(arrayOf(
            Config.coreutilsTimeout, "--signal=6", Config.timeout,
            Config.dReal, "--precision", precision.toString(), tempFile.absolutePath)
    )
    val output = process.inputStream.bufferedReader().readLines()
    return when {
        output.isEmpty() -> false.also {
            //println("TIMEOUT")/*; println(query)*/
            if (timeouts.incrementAndGet() % 100 == 0) println("Timeouts: ${timeouts.get()}")
        }  // returned when killed by timeout
        output.last() == "unsat" -> true
        "delta-sat" !in output.last() -> {
            println(query)
            error("Solver failed: $output")
        }
        else -> false
    }.also {
        tempFile.delete()   // JVM is not clearing temp files automatically.
    }
}

fun makeQuery(query: String) =
"""
(set-logic QF_NRA_ODE)
$query
(check-sat)
(exit)
""".trim()


inline fun DoubleArray.findInterval(action: (a: Double, b: Double) -> Boolean): Pair<Double, Double>? {
    return (0 until this.size).step(2)
            .firstOrNull { action(this[it], this[it +1]) }
            ?.let { this[it] to this[it +1] }
}

inline fun <reified R> DoubleArray.mapIntervals(action: (a: Double, b: Double) -> R): Array<R> {
    return Array(this.size / 2) { i ->
        action(this[2*i], this[2*i + 1])
    }
}

suspend inline fun <T: Any, R: Any> List<T>.mapParallel(crossinline  action: (T) -> R): List<R> {
    val lastPrint = AtomicLong(0L)
    val progress = AtomicInteger(0)
    return this.map { async(Config.threadPool) {
        action(it).also {
            progress.incrementAndGet()
            val last = lastPrint.get()
            val current = System.currentTimeMillis()
            if (current > last + 1000 && lastPrint.compareAndSet(last, current)) {
                println("Progress: ${progress.get()} / ${this@mapParallel.size}")
            }
        }
    } }
    .map { it.await() }
}

suspend inline fun <T: Any> List<T>.filterParallel(crossinline  action: (T) -> Boolean): List<T>
    = this.mapParallel { it to action(it) }.mapNotNull { (i, b) -> if (b) i else null }