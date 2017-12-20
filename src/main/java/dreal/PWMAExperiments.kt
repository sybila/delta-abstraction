package dreal

import com.github.sybila.ode.generator.NodeEncoder
import com.github.sybila.ode.model.OdeModel
import com.github.sybila.ode.model.Parser
import svg.toSvgImage
import java.io.File
import kotlin.coroutines.experimental.buildSequence

private fun OdeModel.split(steps: Int): OdeModel {
    val stepSize = variables
            .map { it.range  }.map { (l, h) -> (h - l) / steps.toDouble() }
            .min()!!

    val thresholds = variables.map {
        val (l, h) = it.range
        buildSequence {
            var t = l
            do {
                yield(t)
                t += stepSize
            } while (t < (h - stepSize/2))
            yield(h)
        }.toList()
    }

    return OdeModel(variables.mapIndexed { i, v -> v.copy(thresholds = thresholds[i]) })
}

fun main(args: Array<String>) {

    val odeModel = Parser().parse(File(Config.projectRoot, "model.bio")).split(50)

    val TS = odeModel.exportTransitionSystem()

    val tX = odeModel.variables[0].thresholds
    val tY = odeModel.variables[1].thresholds

    val encoder = NodeEncoder(odeModel)

    val eqLow = TS.states.filter { s ->
        val (x,y) = encoder.decodeNode(s)
        tX[x] <= 5.03 && 5.03 <= tX[x+1] && tY[y] <= 0.8 && 0.8 <= tY[y+1]
    }.toSet()

    val eqHigh = TS.states.filter { s ->
        val (x,y) = encoder.decodeNode(s)
        tX[x] <= 6.15 && 6.15 <= tX[x+1] && tY[y] <= 4.51 && 4.51 <= tY[y+1]
    }.toSet()

    val reachLow = TS.reachSet(eqLow, false)
    val reachHigh = TS.reachSet(eqHigh, false)

    val both = reachLow.intersect(reachHigh)

    val volume = both.map { s ->
        val (x,y) = encoder.decodeNode(s)
        val width = tX[x+1] - tX[x]
        val height = tY[y+1] - tY[y]
        width * height
    }.sum()

    val terminalRectangles = both.map { s ->
        val (x,y) = encoder.decodeNode(s)
        Rectangle(doubleArrayOf(tX[x], tX[x+1], tY[y], tY[y+1]))
    }

    val partitioning = odeModel.granularPartitioning(50)
    val image = partitioning.toSvgImage(terminalRectangles.toSet())

    val output = File(Config.projectRoot, "prop.pwma.svg")
    output.writeText(image.normalize(Config.targetWidth).compileSvg())

    println("Terminal: $both")

    println("Volume: $volume")
}