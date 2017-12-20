package dreal

import kotlinx.coroutines.experimental.runBlocking
import svg.toSvgImage
import java.io.DataInputStream
import java.io.File

fun G1Sexperiments(faceSplit: Int, granularity: Int) {
    val partitioningFile = File(Config.projectRoot, "partitioning.$granularity.data")
    val partitioning = DataInputStream(partitioningFile.inputStream()).use { it.readPartitioning() }

    val stateFile = File(Config.projectRoot, "states.$granularity.$faceSplit.data")
    val states = DataInputStream(stateFile.inputStream()).use { it.readStates() }

    val transitionFile = File(Config.projectRoot, "transitions.$granularity.$faceSplit.data")
    val transitions = DataInputStream(transitionFile.inputStream()).use { it.readTransitions() }

    val TS = TransitionSystem(states, transitions)

    val stableLow = TS.states.filter { it is State.Interior && it.rectangle.contains(0, 5.03) && it.rectangle.contains(1, 0.8) }
    val stableHigh = TS.states.filter { it is State.Interior && it.rectangle.contains(0, 6.15) && it.rectangle.contains(1, 4.51) }

    val propL = TS.reachSet(stableLow.toSet(), time = false)

    val propH = TS.reachSet(stableHigh.toSet(), time = false)

    val prop = propL.intersect(propH)

    val propRect = prop.mapNotNull {
        when (it) {
            is State.Exterior -> null
            is State.Interior -> it.rectangle
            is State.Transition -> it.to
        }
    }.toSet()

    val volume = propRect.map { it.volume }.sum()

    println("Vol: $volume")

    val image = partitioning.toSvgImage(propRect)

    val output = File(Config.projectRoot, "prop.$granularity.$faceSplit.svg")
    output.writeText(image.normalize(Config.targetWidth).compileSvg())
}

fun main(args: Array<String>) {
    runBlocking {
        //G1Sexperiments(0, 50)
        //G1Sexperiments(1, 50)
        G1Sexperiments(2, 50)
    }
}