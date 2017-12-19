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

    var i = 0
    do {
        val old = partitioning
        partitioning = model.refineUnsafe(partitioning)

        i += 1
        val image = partitioning.toSvgImage(partitioning.items.mapNotNull { if (it.isSafe) null else it.bounds }.toSet())

        val output = File(Config.projectRoot, "partitioning.$i.svg")
        output.writeText(image.normalize(Config.targetWidth).compileSvg())
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

fun main(args: Array<String>) {
    runBlocking {
        //computePartitioning(10)
        computeStates(0, 50)
        computeStates(1, 50)
        computeStates(2, 50)
    }
}