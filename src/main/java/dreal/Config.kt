package dreal

import kotlinx.coroutines.experimental.newFixedThreadPoolContext
import java.io.File

/**
 *
 */

object Config {

    /**
     * The directory which contains the project files.
     */
    val projectRoot = "g1s/"

    /**
     * Target SVG image size.
     */
    val targetWidth = 1000.0

    /**
     * Thread pool for executing all hard work.
     */
    val threadPool = newFixedThreadPoolContext(Runtime.getRuntime().availableProcessors(), "worker")

    val tMax: Double = 2.0

    val skew: Double = 1.0
    val granularity = 30.0

    val dReal = "/usr/local/bin/dreal"
    val coreutilsTimeout = "/usr/local/bin/gtimeout"

    val timeout = "10s"

    val partitionPrecision = 0.001

    fun projectFile(name: String) = File(projectRoot, name)
}