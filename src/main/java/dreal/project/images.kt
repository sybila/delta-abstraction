package dreal.project

import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.Parser
import com.google.gson.reflect.TypeToken
import dreal.State
import dreal.Task
import dreal.project.delta.DeltaTransitionSystemTask
import dreal.project.pwma.ApproximationTask
import dreal.project.pwma.RectangularPartitioningTask
import svg.DeltaImage
import svg.PwmaImage
import svg.SvgImage
import java.io.File

object RectangularPartitioningSvg : Task(RectangularPartitioningTask) {

    override val output: File = File(projectRoot, "partition.pwma.svg")

    override fun run() {
        val partition = json.fromJson(RectangularPartitioningTask.output.readText(), Partitioning::class.java)

        output.writeText(SvgImage(partition.items.map { it.bounds.toSvgRectangle() }, 0.0)
                .normalize(targetWidth)
                .compileSvg()
        )
    }
}

object RectangularTransitionSystemSvg : Task(ApproximationTask) {

    override val output: File = File(projectRoot, "ts.pwma.svg")

    override fun run() {
        val model = Parser().parse(ApproximationTask.output.readText())
        if (model.variables.size != 2) error("Cannot render model with ${model.variables.size} dimensions.")
        val ts = RectangleOdeModel(model, true)

        output.writeText(PwmaImage(model, ts, emptyMap()).toSvgImage().normalize(targetWidth).compileSvg())
    }

}

object DeltaTransitionSystemSvg : Task(DeltaTransitionSystemTask, RectangularPartitioningTask) {
    override val output: File = File(projectRoot, "ts.delta.svg")

    override fun run() {
        val partitioning = json.fromJson(RectangularPartitioningTask.output.readText(), Partitioning::class.java)
        val type = object : TypeToken<TransitionSystem<State>>() {}.type
        val system = json.fromJson<TransitionSystem<State>>(DeltaTransitionSystemTask.output.readText(), type)

        output.writeText(DeltaImage(partitioning, system, emptySet()).toSvgImage().normalize(targetWidth).compileSvg())
    }
}