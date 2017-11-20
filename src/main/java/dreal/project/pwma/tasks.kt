package dreal.project.pwma

import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.Parser
import com.github.sybila.ode.model.computeApproximation
import com.github.sybila.ode.model.toBio
import dreal.Task
import dreal.project.*
import svg.PwmaImage
import java.io.File

object ApproximationTask : Task(ModelFile) {

    override val output: File = File(projectRoot, "model.pwma.bio")

    override fun run() {
        val model = Parser().parse(ModelFile.output)
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
        output.writeText(approximation.toBio())
    }

}

object RectangularPartitioningTask : Task(ApproximationTask) {

    override val output: File = File(projectRoot, "partition.pwma.json")

    override fun run() {
        val model = Parser().parse(ApproximationTask.output)
        output.writeText(json.toJson(model.exportPartitioning()))
    }

}

object RectangularTransitionSystemTask : Task(ApproximationTask) {

    override val output: File = File(projectRoot, "ts.pwma.json")

    override fun run() {
        val model = Parser().parse(ApproximationTask.output)
        output.writeText(json.toJson(model.exportTransitionSystem()))
    }
}

object RectangularTerminalComponentsSvg : Task(RectangularTransitionSystemTask, ApproximationTask) {

    override val output: File = File(projectRoot, "terminal.pwma.svg")

    override fun run() {
        val model = Parser().parse(ApproximationTask.output)
        val ts = json.fromJson<TransitionSystem<Int>>(RectangularTransitionSystemTask.output.readText(), TransitionSystem::class.java)

        val terminal = ts.terminalComponents()

        output.writeText(PwmaImage(model, RectangleOdeModel(model), mapOf("#ffaaff" to terminal))
                .toSvgImage()
                .normalize(targetWidth)
                .compileSvg()
        )

    }
}