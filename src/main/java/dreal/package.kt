package dreal

import dreal.project.Config
import java.io.File

fun provedUnsat(query: String, precision: Double = 0.001): Boolean {
    val tempFile = File.createTempFile("input", ".smt2")
    tempFile.writeText(query)
    val process = Runtime.getRuntime().exec(arrayOf(
            Config.coreutilsTimeout, "--signal=6", Config.timeout,
            Config.dReal, "--precision", precision.toString(), tempFile.absolutePath)
    )
    val output = process.inputStream.bufferedReader().readLines()
    return when {
        output.last() == "unsat" -> true
        output.isEmpty() -> false   // returned when killed by timeout
        "delta-sat" !in output.last() -> error("Solver failed: $output")
        else -> false
    }
}

fun makeQuery(query: String) =
"""
(set-logic QF_NRA_ODE)
$query
(check-sat)
(exit)
""".trim()

