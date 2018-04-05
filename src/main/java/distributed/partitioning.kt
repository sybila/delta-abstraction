package distributed

import com.github.daemontus.tokenizer.parseLines
import com.github.daemontus.validate
import dreal.*
import java.io.File
import java.util.Comparator

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
private fun File.partitioningFile() = File(this, "partitioning.data")
private fun File.statesFolder() = File(this, "states")
private fun File.statesFile() = File(this, "states.data")
private fun File.iterationFolder(iteration: Int) = File(this, "p_$iteration")

// state job files
private fun File.stateJobInput(jobId: Int) = File(this, "job.$jobId.in.data")
private fun File.stateJobOutput(jobId: Int) = File(this, "job.$jobId.out.data")
private fun File.stateJobScript() = File(this, "jobs.sh")

// partitioning iteration files
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

private fun File.readStates(): List<State> = this.dataInputStream().use {
    it.readStates()
}

private fun File.writeStates(states: List<State>) = this.dataOutputStream().use {
    it.writeStates(states)
}

fun generateStateJobs(experiment: File) {
    val statesFolder = experiment.statesFolder()
    statesFolder.mkdirs()
    val partitioning = experiment.partitioningFile().readPartitioning()

    val faceSplit = 0

    experiment.modelFile().loadModel().toModelFactory().run {
        val boundsRect = Rectangle(DoubleArray(dimensions * 2) { it ->
            val d = it / 2; if (it % 2 == 0) dimensionBounds(d).first else dimensionBounds(d).second
        })

        val facetStates = partitioning.items.toList().mapIndexed { i, (rOut, _) ->
            if (i % 1000 == 0) println("Progress: $i/${partitioning.items.size}")
            val adjacent = ArrayList<State.Transition>()
            for ((rIn, _) in partitioning.items) {
                rOut.takeIf { it != rIn }?.getFacetIntersection(rIn)?.let { (facet, _, _) ->
                    var facets = listOf(facet)
                    repeat(faceSplit) {
                        facets = facets.flatMap { it.split() }
                    }
                    facets.forEach { face ->
                        adjacent.add(State.Transition(rOut, rIn, face))
                    }
                }
            }
            boundsRect.facets.forEach { external ->
                rOut.getFacetIntersection(external)?.let { (facet, _, _) ->
                    adjacent.add(State.Transition(rOut, external, facet))
                    adjacent.add(State.Transition(external, rOut, facet))
                }
            }
            adjacent
        }.flatMap { it }

        println("Facet states: ${facetStates.size}")
        val batchSize = ((facetStates.size / 500) + 1)
        println("Batch size: $batchSize")
        val batchCount = Math.ceil(facetStates.size.toDouble() / batchSize).toInt()
        for (batch in 0 until batchCount) {
            val states = facetStates.subList(batch * batchSize, ((batch+1) * batchSize).coerceAtMost(facetStates.size))
            statesFolder.stateJobInput(batch).writeStates(states)
        }

        statesFolder.stateJobScript().writeText("""
        #!/bin/bash
        #PBS -l select=1:ncpus=1:mem=1gb:scratch_local=1gb
        #PBS -l walltime=2:00:00

        module add jdk-8

        /storage/brno2/home/daemontus/delta-experiments/v1/bin/delta-abstraction s2-run-job ${experiment.absolutePath} ${"$"}PBS_ARRAY_INDEX
        """.trimIndent())
    }

}

fun runStatesJob(experiment: File, jobId: Int) {
    val states = experiment.statesFolder().stateJobInput(jobId).readStates().filterIsInstance<State.Transition>()
    experiment.modelFile().loadModel().toModelFactory().run {
        experiment.statesFolder().stateJobOutput(jobId).writeStates(states.filter { (from, to, via) ->
            val (_, d, positive) = from.getFacetIntersection(to)!!
            maybeHasFlow(via, d, positive)
        })
    }
}

fun mergeStates(experiment: File) {
    val statesFolder = experiment.statesFolder()

    val partitioning = experiment.partitioningFile().readPartitioning()

    val states = ArrayList<State>()

    var jobId = 0
    var jobResult = statesFolder.stateJobOutput(jobId)
    while (jobResult.exists()) {
        val data = jobResult.readStates()
        states.addAll(data)
        jobId += 1
        jobResult = statesFolder.stateJobOutput(jobId)
    }

    val unsafeInterior = partitioning.items.filter { !it.isSafe }.map { State.Interior(it.bounds) }
    states.add(State.Exterior)
    states.addAll(unsafeInterior)

    println("Total states: ${states.size}")

    experiment.statesFile().writeStates(states)
}


fun generatePartitioning(experiment: File, granularity: Int) {
    experiment.iterationFolder(0).mkdirs()  //mkdirs
    val model = experiment.modelFile().loadModel()
    val partitioning = model.granularPartitioning(granularity)
    println("Created partitioning with size: ${partitioning.items.size}")
    experiment.iterationFolder(0).inputPartitioning().writePartitioning(partitioning)
}

fun preparePartitioningJobs(experiment: File, iteration: Int) {
    val iFolder = experiment.iterationFolder(iteration)
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

    println("Final partitioning size: ${items.size}")

    val nextIteration = experiment.iterationFolder(iteration + 1)
    nextIteration.mkdirs()

    nextIteration.inputPartitioning().writePartitioning(Partitioning(items))
    iFolder.outputPartitioning().writePartitioning(Partitioning(items))
}