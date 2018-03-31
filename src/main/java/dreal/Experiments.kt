package dreal
import com.github.daemontus.tokenizer.parseLines
import com.github.daemontus.validate
import com.github.sybila.ode.model.Parser
import kotlinx.coroutines.experimental.runBlocking
import svg.DeltaImage
import svg.toSvgImage
import java.io.*
import kotlin.system.measureTimeMillis

//private fun getModel() = Parser().parse(File(Config.projectRoot, "model.bio"))

private fun getModel() = File(Config.projectRoot, "model.ode").useLines {
    it.toList().parseLines().validate()
}

suspend fun computePartitioning(granularity: Int) {
    val odeModel = getModel()
    val model = odeModel.toModelFactory()

    var partitioning = odeModel.granularPartitioning(granularity)// Partitioning(setOf(Partitioning.Item(boundsRect)))

    //var i = 0
    do {
        val old = partitioning
        partitioning = model.refineUnsafe(partitioning)

        /*i += 1
        val image = partitioning.toSvgImage(partitioning.items.mapNotNull { if (it.isSafe) null else it.bounds }.toSet())

        val output = File(Config.projectRoot, "partitioning.$i.svg")
        output.writeText(image.normalize(Config.targetWidth).compileSvg())*/
    } while (old != partitioning)

    val output = File(Config.projectRoot, "partitioning.$granularity.data")
    output.dataOutputStream().use {
        it.writePartitioning(partitioning)
    }
}

suspend fun computeStates(faceSplit: Int, granularity: Int) {
    val odeModel = getModel()
    val model = odeModel.toModelFactory()

    val partitioningFile = File(Config.projectRoot, "partitioning.$granularity.data")
    val partitioning = partitioningFile.dataInputStream().use { it.readPartitioning() }

    val states = model.buildStateSpace(partitioning, faceSplit)

    /*val imgOutput = File(Config.projectRoot, "states.svg")
    val image = DeltaImage(partitioning, TransitionSystem(states, emptyList()), emptySet())
    imgOutput.writeText(image.toSvgImage().normalize(Config.targetWidth).compileSvg())*/

    val output = File(Config.projectRoot, "states.$granularity.$faceSplit.data")
    output.dataOutputStream().use {
        it.writeStates(states)
    }
}

suspend fun computeTransitions(faceSplit: Int, granularity: Int) {
    val odeModel = getModel()
    val model = odeModel.toModelFactory()

    println("Reading old system.")

    val oldTS = if (faceSplit == 0) {
        TransitionSystem(emptyList(), emptyList())
    } else {
        val oldStateFile = File(Config.projectRoot, "states.$granularity.${faceSplit - 1}.data")
        val oldStates = oldStateFile.dataInputStream().use { it.readStates() }

        val oldTransitionFile = File(Config.projectRoot, "transitions.$granularity.${faceSplit - 1}.data")
        val oldTransitions = oldTransitionFile.dataInputStream().use { it.readTransitions() }

        TransitionSystem(oldStates, oldTransitions)
    }


    val partitioningFile = File(Config.projectRoot, "partitioning.$granularity.data")
    val partitioning = partitioningFile.dataInputStream().use { it.readPartitioning() }

    println("Reading states.")

    val stateFile = File(Config.projectRoot, "states.$granularity.$faceSplit.data")
    val states = stateFile.dataInputStream().use { it.readStates() }

    val transitions = model.buildTransitions(oldTS, partitioning, states)

    //val imgOutput = File(Config.projectRoot, "transitions.svg")
    //val image = DeltaImage(partitioning, TransitionSystem(states, transitions), emptySet())
    //imgOutput.writeText(image.toSvgImage().normalize(Config.targetWidth).compileSvg())

    val output = File(Config.projectRoot, "transitions.$granularity.$faceSplit.data")
    output.dataOutputStream().use {
        it.writeTransitions(transitions)
    }
}

fun computeTerminalComponents(faceSplit: Int, granularity: Int) {
    val partitioningFile = File(Config.projectRoot, "partitioning.$granularity.data")
    val partitioning = partitioningFile.dataInputStream().use { it.readPartitioning() }

    val stateFile = File(Config.projectRoot, "states.$granularity.$faceSplit.data")
    val states = stateFile.dataInputStream().use { it.readStates() }

    val transitionFile = File(Config.projectRoot, "transitions.$granularity.$faceSplit.data")
    val transitions = transitionFile.dataInputStream().use { it.readTransitions() }

    val TS = TransitionSystem(states, transitions)

    val terminalComponents = TS.terminalComponents()

    println("Computed")

    val terminalRectangles: Set<Rectangle> = terminalComponents.mapNotNullTo(HashSet()) {
        when (it) {
            is State.Exterior -> null
            is State.Interior -> it.rectangle
            is State.Transition -> it.to
        }
    }.toSet()

    println("Volume: ${terminalRectangles.map { it.volume }.sum()}")
/*
    if (partitioning.items.first().bounds.dimensions == 2) {
        val image = partitioning.toSvgImage(terminalRectangles.toSet())

        val output = File(Config.projectRoot, "terminal.$granularity.$faceSplit.svg")
        output.writeText(image.normalize(Config.targetWidth).compileSvg())
    } else {
        val zThresholds = partitioning.items.asSequence().flatMap {
            sequenceOf(it.bounds.lBound(2), it.bounds.hBound(2))
        }.toSet().sorted()
        zThresholds.forEachIndexed { i, z ->
            val output = File(Config.projectRoot, "$i.$z.terminal.$granularity.$faceSplit.svg")

            val newPartition = Partitioning(partitioning.items.filter { it.bounds.contains(2, z) }.map { it.copy(bounds =
                it.bounds.project(2)
            ) }.toSet())

            val newProp = terminalRectangles.filter { it.contains(2, z) }.map { it.project(2) }

            val image = newPartition.toSvgImage(newProp.toSet())
            output.writeText(image.normalize(Config.targetWidth).compileSvg())
        }

        val output = File(Config.projectRoot, "terminal.$granularity.$faceSplit.py")

        val commands = terminalRectangles.mapIndexed { i, r ->
            val location = DoubleArray(3) { i ->
                (r.lBound(i) + r.hBound(i)) / 2
            }.joinToString(separator = ",")
            val proportions = DoubleArray(3) { i ->
                val size = r.hBound(i) - r.lBound(i)
                size/2  // default cube has size 2
            }.joinToString(separator = ",")
            //println("Rectangle $r at $location with resize $proportions")
"""
bpy.ops.mesh.primitive_cube_add(location=($location))
bpy.ops.transform.resize(value=($proportions))
bpy.context.active_object.data.materials.append(solid)
print('$i/${terminalRectangles.size}')
"""

        }

        val script =
"""
import bpy

solid = bpy.data.materials.get("solid")
if solid is None:
        solid = bpy.data.materials.new(name = "solid")
        solid.diffuse_color = (0.8, 0.8, 1.0)
        solid.specular_intensity = 0.0
        solid.emit = 0.5

wire = bpy.data.materials.get("wire")
if wire is None:
        wire = bpy.data.materials.new(name = "wire")
        wire.type = 'WIRE'
        wire.diffuse_color = (0.0, 0.0, 0.0)
        wire.specular_intensity = 0.0
        wire.offset_z = 0.01
        wire.use_transparency = True
        wire.emit = 0.5

${commands.joinToString(separator = "\n")}
"""
        output.writeText(script)
    }*/
}

private suspend fun experiments(granularity: Int) {
    val odeModel = getModel()
    val model = odeModel.toModelFactory()

    var partitioning = odeModel.granularPartitioning(granularity)

    val zeros = partitioning.items.toList().filterParallel {
        model.maybeHasZero(it.bounds)
    }
    println("zeros: ${zeros.size}")
    println(zeros)
}

fun main(args: Array<String>) {
    runBlocking {
        val partitioningFile = File(Config.projectRoot, "partitioning.20.data")
        val partitioning = partitioningFile.dataInputStream().use { it.readPartitioning() }
        val unsafeVolume = partitioning.items.map { if (it.isSafe) 0.0 else it.bounds.volume }.sum()
        println("Unsafe volume: $unsafeVolume")
        //experiments(20)
        //computePartitioning(20)
        /*val elapsed = measureTimeMillis {
            //computePartitioning(20)
            computeStates(2, 20)
            println("========== States computed ==========")
            computeTransitions(2, 20)
            //println("========== Transitions computed ==========")
            //computeTerminalComponents(1, 20)
        }
        println("Solver calls ${Config.solverCalls.get()} in $elapsed")*/
        /*computePartitioning(20)
        computeStates(0, 20)
        computeTransitions(0, 20)
        computeTerminalComponents(0, 20)*/
        /*computeStates(1, 50)
        computeTransitions(1, 50)
        computeTerminalComponents(1, 50)
        computeStates(2, 50)
        computeTransitions(2, 50)
        computeTerminalComponents(2, 50)*/
    }
}

fun File.dataInputStream(): DataInputStream = DataInputStream(BufferedInputStream(this.inputStream()))
fun File.dataOutputStream(): DataOutputStream = DataOutputStream(BufferedOutputStream(this.outputStream()))