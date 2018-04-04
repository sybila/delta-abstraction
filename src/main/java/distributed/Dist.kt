package distributed

import dreal.experimentsMain
import java.io.File

fun main(args: Array<String>) {
    if (args.isEmpty()) experimentsMain(args)
    else {
        when (args[0]) {
            "p0-generate" -> generatePartitioning(File(args[1]), args[2].toInt())
            "p1-prepare-jobs" -> preparePartitioningJobs(File(args[1]), args[2].toInt())
            "p2-run-job" -> runPartitioningJob(File(args[1]), args[2].toInt(), args[3].toInt())
            "p3-merge" -> mergePartitioningJobs(File(args[1]), args[2].toInt())
        }
    }
}