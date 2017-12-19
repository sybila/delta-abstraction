package dreal
import com.github.sybila.ode.model.Parser
import kotlinx.coroutines.experimental.runBlocking
import svg.toSvgImage
import java.io.DataInputStream
import java.io.DataOutputStream
import java.io.File

suspend fun computePartitioning(granularity: Int) {
    val odeModel = Parser().parse(File(Config.projectRoot, "model.bio"))
    val model = odeModel.toModelFactory()

    //val boundsRect = Rectangle(odeModel.variables.flatMap { listOf(it.range.first, it.range.second) }.toDoubleArray())
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
    DataOutputStream(output.outputStream()).use {
        it.writePartitioning(partitioning)
    }
}

suspend fun computeStates(faceSplit: Int, granularity: Int) {
    val odeModel = Parser().parse(File(Config.projectRoot, "model.bio"))
    val model = odeModel.toModelFactory()

    val partitioningFile = File(Config.projectRoot, "partitioning.$granularity.data")
    val partitioning = DataInputStream(partitioningFile.inputStream()).use { it.readPartitioning() }

    val states = model.buildStateSpace(partitioning, faceSplit)

    /*val imgOutput = File(Config.projectRoot, "states.svg")
    val image = DeltaImage(partitioning, TransitionSystem(states, emptyList()), emptySet())
    imgOutput.writeText(image.toSvgImage().normalize(Config.targetWidth).compileSvg())*/

    val output = File(Config.projectRoot, "states.$granularity.$faceSplit.data")
    DataOutputStream(output.outputStream()).use {
        it.writeStates(states)
    }
}

suspend fun computeTransitions(faceSplit: Int, granularity: Int) {
    val odeModel = Parser().parse(File(Config.projectRoot, "model.bio"))
    val model = odeModel.toModelFactory()

    val partitioningFile = File(Config.projectRoot, "partitioning.$granularity.data")
    val partitioning = DataInputStream(partitioningFile.inputStream()).use { it.readPartitioning() }

    val stateFile = File(Config.projectRoot, "states.$granularity.$faceSplit.data")
    val states = DataInputStream(stateFile.inputStream()).use { it.readStates() }

    val transitions = model.buildTransitions(partitioning, states)

    /*val imgOutput = File(Config.projectRoot, "transitions.svg")
    val image = DeltaImage(partitioning, TransitionSystem(states, transitions), emptySet())
    imgOutput.writeText(image.toSvgImage().normalize(Config.targetWidth).compileSvg())*/

    val output = File(Config.projectRoot, "transitions.$granularity.$faceSplit.data")
    DataOutputStream(output.outputStream()).use {
        it.writeTransitions(transitions)
    }
}

fun computeTerminalComponents(faceSplit: Int, granularity: Int) {
    val partitioningFile = File(Config.projectRoot, "partitioning.$granularity.data")
    val partitioning = DataInputStream(partitioningFile.inputStream()).use { it.readPartitioning() }

    val stateFile = File(Config.projectRoot, "states.$granularity.$faceSplit.data")
    val states = DataInputStream(stateFile.inputStream()).use { it.readStates() }

    val transitionFile = File(Config.projectRoot, "transitions.$granularity.$faceSplit.data")
    val transitions = DataInputStream(transitionFile.inputStream()).use { it.readTransitions() }

    val TS = TransitionSystem(states, transitions)

    val terminalComponents = TS.terminalComponents()

    val terminalRectangles = terminalComponents.mapNotNull {
        when (it) {
            is State.Exterior -> null
            is State.Interior -> it.rectangle
            is State.Transition -> it.to
        }
    }

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
    }
}

fun main(args: Array<String>) {
    runBlocking {
        //computePartitioning(10)
        //computeStates(1, 10)
        //computeTransitions(1, 10)
        computePartitioning(10)
        computeStates(0, 10)
        computeTransitions(0, 10)
        computeTerminalComponents(0, 10)
        /*computeStates(1, 50)
        computeTransitions(1, 50)
        computeTerminalComponents(1, 50)
        computeStates(2, 50)
        computeTransitions(2, 50)
        computeTerminalComponents(2, 50)*/
    }
}