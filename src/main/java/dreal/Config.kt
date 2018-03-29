package dreal

import kotlinx.coroutines.experimental.newFixedThreadPoolContext
import java.io.File
import java.util.concurrent.atomic.AtomicLong

/**
 *
 */

object Config {

    /**
     * The directory which contains the project files.
     */
    val projectRoot = "clark/"

    /**
     * Target SVG image size.
     */
    val targetWidth = 1000.0

    /**
     * Thread pool for executing all hard work.
     */
    val threadPool = newFixedThreadPoolContext(Runtime.getRuntime().availableProcessors(), "worker")

    val tMax: Double = 0.2

    val skew: Double = 1.0
    val granularity = 30.0

    val dReal = "/usr/local/bin/dreal"
    val coreutilsTimeout = "/usr/local/bin/gtimeout"

    val timeout = "20s"

    val partitionPrecision = 1e-10

    fun projectFile(name: String) = File(projectRoot, name)

    val solverCalls = AtomicLong(0)
}