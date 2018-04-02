package distributed

import com.github.daemontus.tokenizer.parseLines
import com.github.daemontus.validate
import dreal.*
import java.io.File

/**
 * The process of computing distributed partitioning works as follows:
 *
 * 0) Initial partitioning is generated into a file
 * 1) Unsafe state from a partitioning are loaded, split and distributed into N files.
 * 2) Each file is processed on one machine distributively.
 * 3) Files are merged into a single partitioning.
 * 4) Go to 1.
 *
 */

private fun File.loadModel() = this.useLines { it.toList().parseLines().validate() }

fun generatePartitioning(modelFile: File, granularity: Int, output: File) {
    println("prepare partitioning!")
    val model = modelFile.loadModel()
    val partitioning = model.granularPartitioning(granularity)
    output.dataOutputStream().use {
        it.writePartitioning(partitioning)
    }
}

fun prepareJobs(partitioningFile: File, jobCount: Int, targetFolder: File) {
    println("prepare jobs!")
    val partitioning = partitioningFile.dataInputStream().use {
        it.readPartitioning()
    }

    val unsafe = partitioning.items.filter { !it.isSafe }
    println("Unsafe: ${unsafe.size}")
    val refinedRectangles = unsafe.flatMap { (r, _) -> r.split() }.shuffled()   // shuffle for better load balancing
    println("After refine: ${refinedRectangles.size}")

    val batchSize = (refinedRectangles.size / jobCount) + 1
    println("Batch size: $batchSize")

    var batchStart = 0
    var batch = 0
    while (batchStart < refinedRectangles.size) {
        val batchRectangles = refinedRectangles.subList(batchStart, (batchStart + batchSize).coerceAtMost(refinedRectangles.size))
        val batchPartitioning = Partitioning(batchRectangles.map { Partitioning.Item(it) }.toSet())
        File(targetFolder, "job.$batch.data").dataOutputStream().use {
            it.writePartitioning(batchPartitioning)
        }
        batchStart += batchSize
        batch += 1
    }
}

fun runJob(modelFile: File, dataFolder: File, jobId: Int) {
    val partitioning = File(dataFolder, "job.$jobId.data").dataInputStream().use {
        it.readPartitioning()
    }

    modelFile.loadModel().toModelFactory().run {
        val eval = partitioning.items.map { (r, _) ->
            if (isSafeWithin(r, Config.tMax)) {
                Partitioning.Item(r, Config.tMax)
            } else {
                Partitioning.Item(r)
            }
        }
        File(dataFolder,"result.$jobId.data").dataOutputStream().use {
            it.writePartitioning(Partitioning(eval.toSet()))
        }
    }
}

fun mergeJobs(partitioningFile: File, jobCount: Int, dataFolder: File) {
    println()
    val result = HashSet<Partitioning.Item>()

    for (jobId in 0 until jobCount) {
        val (data) = File(dataFolder, "result.$jobId.data").dataInputStream().use {
            it.readPartitioning()
        }
        result.addAll(data)
    }

    partitioningFile.dataOutputStream().use {
        it.writePartitioning(Partitioning(result))
    }
}