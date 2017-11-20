package dreal.project.delta

import com.github.sybila.ode.model.Parser
import com.google.gson.reflect.TypeToken
import dreal.State
import dreal.Task
import dreal.makeStateSpace
import dreal.project.Partitioning
import dreal.project.TransitionSystem
import dreal.project.json
import dreal.project.projectRoot
import dreal.project.pwma.ApproximationTask
import dreal.project.pwma.RectangularPartitioningTask
import dreal.toModelFactory
import java.io.File

object DeltaTransitionSystemTask : Task(ApproximationTask, RectangularPartitioningTask) {

    override val output: File = File(projectRoot, "ts.delta.json")

    override fun run() {
        val ode = Parser().parse(ApproximationTask.output)
        val model = ode.toModelFactory()
        val partitioning = json.fromJson(RectangularPartitioningTask.output.readText(), Partitioning::class.java)

        val ts = model.makeStateSpace(partitioning)

        output.writeText(json.toJson(ts.system, object : TypeToken<TransitionSystem<State>>() {}.type))
    }
}