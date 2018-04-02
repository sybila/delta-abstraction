package distributed

import dreal.experimentsMain
import java.io.File

fun main(args: Array<String>) {
    if (args.isEmpty()) experimentsMain(args)
    else {
        when (args[0]) {
            "0-partitioning-generate" -> generatePartitioning(File(args[1]), args[2].toInt(), File(args[3]))
            "1-partitioning-prepare-jobs" -> prepareJobs(File(args[1]), args[2].toInt(), File(args[3]))
            "2-partitioning-run-job" -> runJob(File(args[1]), File(args[2]), args[3].toInt())
            "3-partitioning-merge" -> mergeJobs(File(args[1]), args[2].toInt(), File(args[3]))
        }
    }
}