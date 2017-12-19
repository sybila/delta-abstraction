package dreal
import com.github.sybila.ode.model.Parser
import kotlinx.coroutines.experimental.runBlocking
import svg.toSvgImage
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

fun main(args: Array<String>) {
    runBlocking {
        computePartitioning(50)
    }
}