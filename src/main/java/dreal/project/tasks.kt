package dreal.project

import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.computeApproximation
import dreal.State
import dreal.makeStateSpace
import dreal.toModelFactory
import svg.PwmaImage

object ModelFile : BioTask("model.bio")

object PWMA {

    object Approximation : BioTask("model.pwma.bio", ModelFile) {
        override fun run() {
            val model = ModelFile.readBio()
            val approximation = model.computeApproximation(fast = false, cutToRange = true).run {
                // make new uniform thresholds in variables which have no cuts and have var points set
                copy(variables = variables.map {
                    val expected = it.varPoints?.second ?: 2
                    if (it.thresholds.size != 2) it else {
                        val (l, h) = it.range
                        val step = (h - l) / expected
                        it.copy(thresholds = (0 until expected).map { l + it * step } + listOf(h))
                    }
                })
            }
            writeBio(approximation)
        }
    }

    object Partition : JsonTask<Partitioning>("partition.pwma.json", type<Partitioning>(), Approximation) {
        override fun run() {
            val model = Approximation.readBio()
            writeJson(model.exportPartitioning())
        }

        object Svg : PartitionSvgTask("partition.pwma.svg", Partition)
    }

    object Transitions : JsonTask<TransitionSystem<Int>>("ts.pwma.json", type<TransitionSystem<Int>>(), Approximation) {
        override fun run() {
            val model = Approximation.readBio()
            writeJson(model.exportTransitionSystem())
        }

        object Svg : SvgTask("ts.pwma.svg", Approximation) {
            override fun run() {
                val model = Approximation.readBio()
                val ts = RectangleOdeModel(model, createSelfLoops = true)
                writeImage(PwmaImage(model, ts, emptyMap()))
            }
        }

    }

    object TerminalComponents : JsonTask<List<Int>>("terminal.pwma.json", type<List<Int>>(), Transitions) {
        override fun run() {
            val ts = Transitions.readJson()
            val terminal = ts.terminalComponents()
            writeJson(terminal.toList())
        }

        object Svg : SvgTask("terminal.pwma.svg", TerminalComponents, Approximation) {
            override fun run() {
                val model = Approximation.readBio()
                val ts = RectangleOdeModel(model, createSelfLoops = true)
                val prop = TerminalComponents.readJson()
                writeImage(PwmaImage(model, ts, mapOf("#ffaaaa" to prop.toSet())))
            }
        }

    }

}

object Delta {

    object Transitions {
        object Rectangular {

            object All : JsonTask<TransitionSystem<State>>("ts.all.delta.rect.json", type<TransitionSystem<State>>(), PWMA.Approximation, PWMA.Partition) {
                override fun run() {
                    val model = PWMA.Approximation.readBio().toModelFactory()
                    val partition = PWMA.Partition.readJson()

                    writeJson(model.makeStateSpace(partition).system)
                }

                object Svg : DeltaTransitionSystemSvgTask("ts.all.delta.rect.svg", PWMA.Partition, All)
            }

            /*object Admissible : JsonTask<TransitionSystem<State>>("ts.admissible.delta.rect.json", type<TransitionSystem<State>>(), PWMA.Approximation, All) {
                override fun run() {
                    val model = PWMA.Approximation.readBio().toModelFactory()
                    val
                }
                object Svg : DeltaTransitionSystemSvgTask("ts.admissible.delta.rect.svg", PWMA.Partition, All)
            }*/

        }

    }

}

fun main(args: Array<String>) {
    PWMA.Approximation
    PWMA.Partition
    PWMA.Partition.Svg
    PWMA.Transitions
    PWMA.Transitions.Svg
    PWMA.TerminalComponents
    PWMA.TerminalComponents.Svg
    Delta.Transitions.Rectangular.All
    Delta.Transitions.Rectangular.All.Svg
    TaskGraph.clean()
    TaskGraph.make()
}