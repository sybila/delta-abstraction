package distributed

import com.github.daemontus.tokenizer.parseLines
import com.github.daemontus.validate
import dreal.*
import java.io.File
import kotlin.math.exp

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

private fun File.modelFile() = File(this, "model.ode")
private fun File.iterationFolder(iteration: Int) = File(this, "p_$iteration")
private fun File.inputPartitioning() = File(this, "p.in.data")
private fun File.outputPartitioning() = File(this, "p.out.data")
private fun File.jobInputFile(jobId: Int) = File(this, "job.$jobId.in.data")
private fun File.jobOutputFile(jobId: Int) = File(this, "job.$jobId.out.data")
private fun File.jobScript() = File(this, "jobs.sh")

private fun File.readPartitioning(): Partitioning = this.dataInputStream().use {
    it.readPartitioning()
}

private fun File.writePartitioning(partitioning: Partitioning) = this.dataOutputStream().use {
    it.writePartitioning(partitioning)
}


fun generatePartitioning(experiment: File, granularity: Int) {
    experiment.iterationFolder(0).mkdirs()  //mkdirs
    val model = experiment.modelFile().loadModel()
    val partitioning = model.granularPartitioning(granularity)
    println("Created partitioning with size: ${partitioning.items.size}")
    experiment.iterationFolder(0).inputPartitioning().writePartitioning(partitioning)
}

fun preparePartitioningJobs(experiment: File, iteration: Int) {
    val iFolder = experiment.iterationFolder(0)
    val partitioning = iFolder.inputPartitioning().readPartitioning()

    val unsafe = partitioning.items.filter { !it.isSafe }
    println("Unsafe items: ${unsafe.size}. Unsafe volume: ${unsafe.map { it.bounds.volume }.sum()}")
    if (unsafe.isEmpty()) {
        println("Nothing to refine!! Partitioning is safe.")
    }
    val refined = unsafe.flatMap { (r, _) -> r.split() }.shuffled()

    val batchSize = ((refined.size / 500) + 1).coerceAtLeast(100)
    println("Batch size: $batchSize")

    val batchCount = Math.ceil(refined.size.toDouble() / batchSize).toInt()
    for (batch in 0 until batchCount) {
        val rectangles = refined.subList(batch * batchSize, ((batch+1) * batchSize).coerceAtMost(refined.size))
        iFolder.jobInputFile(batch).writePartitioning(Partitioning(rectangles.map { Partitioning.Item(it) }.toSet()))
    }
    println("Job count: $batchCount")

    iFolder.jobScript().writeText("""
        #!/bin/bash
        #PBS -l select=1:ncpus=1:mem=1gb:scratch_local=1gb
        #PBS -l walltime=2:00:00

        module add jdk-8

        /storage/brno2/home/daemontus/delta-experiments/v1/bin/delta-abstraction p2-run-job ${experiment.absolutePath} $iteration ${"$"}PBS_ARRAY_INDEX
        """.trimIndent())
}

fun runPartitioningJob(experiment: File, iteration: Int, jobId: Int) {
    val iFolder = experiment.iterationFolder(iteration)
    val partitioning = iFolder.jobInputFile(jobId).readPartitioning()
    val model = experiment.modelFile().loadModel()

    model.toModelFactory().run {
        val eval = partitioning.items.map {
            it.takeUnless { isSafeWithin(it.bounds, Config.tMax) } ?: Partitioning.Item(it.bounds, Config.tMax)
        }
        iFolder.jobOutputFile(jobId).writePartitioning(Partitioning(eval.toSet()))
    }
}

fun mergePartitioningJobs(experiment: File, iteration: Int) {
    val iFolder = experiment.iterationFolder(iteration)

    val originalSafe = iFolder.inputPartitioning().readPartitioning().items.filter { it.isSafe }

    val items = HashSet<Partitioning.Item>(originalSafe)

    var jobId = 0
    var jobResult = iFolder.jobOutputFile(jobId)
    while (jobResult.exists()) {
        val (data) = jobResult.readPartitioning()
        items.addAll(data)
        jobId += 1
        jobResult = iFolder.jobOutputFile(jobId)
    }

    iFolder.outputPartitioning().writePartitioning(Partitioning(items))
}