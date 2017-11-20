package dreal.project

import com.github.sybila.ode.model.OdeModel
import com.github.sybila.ode.model.Parser
import com.github.sybila.ode.model.toBio
import com.google.gson.reflect.TypeToken
import dreal.State
import svg.DeltaImage
import svg.Image
import svg.SvgImage
import java.io.File
import java.lang.reflect.Type

abstract class Task(outputName: String, val dependencies: List<Task>) {

    init {
        @Suppress("LeakingThis")
        TaskGraph.register(this)
    }

    val output: File = Config.projectFile(outputName)

    constructor(outputName: String, vararg dependencies: Task) : this(outputName, dependencies.toList())

    open fun run() {}

    override fun toString(): String = this.javaClass.canonicalName.removePrefix("dreal.project.")
}

abstract class BioTask(outputName: String, dependencies: List<Task>) : Task(outputName, dependencies) {

    constructor(outputName: String, vararg dependencies: Task) : this(outputName, dependencies.toList())

    fun writeBio(model: OdeModel) = output.writeText(model.toBio())

    fun readBio() = Parser().parse(output).let { model ->
        // This is a cleaning step in order to remove rounding duplicates.
        // TODO: Figure out how to avoid this in the original approximation procedure.
        model.copy(variables = model.variables.map {
            it.copy(thresholds = it.thresholds.toSet().sorted())
        })
    }

}

abstract class JsonTask<T>(outputName: String, private val type: Type, dependencies: List<Task>) : Task(outputName, dependencies) {

    constructor(outputName: String, type: Type, vararg dependencies: Task) : this(outputName, type, dependencies.toList())

    fun readJson(): T = Config.json.fromJson(output.readText(), type)

    protected fun writeJson(result: T) {
        output.writeText(Config.json.toJson(result, type))
    }
}

inline fun <reified T> type(): Type = (object : TypeToken<T>() {}).type

abstract class SvgTask(outputName: String, dependencies: List<Task>) : Task(outputName, dependencies) {

    constructor(outputName: String, vararg dependencies: Task) : this(outputName, dependencies.toList())

    protected fun writeSvg(image: SvgImage) {
        output.writeText(image.normalize(Config.targetWidth).compileSvg())
    }

    protected fun writeImage(image: Image) = writeSvg(image.toSvgImage())

}

abstract class PartitionSvgTask(outputName: String, private val task: JsonTask<Partitioning>) : SvgTask(outputName, task) {

    override fun run() {
        val partition = task.readJson()
        writeSvg(SvgImage(partition.items.map { it.bounds.toSvgRectangle() }, 0.0))
    }

}

abstract class DeltaTransitionSystemSvgTask(outputName: String,
                                            private val partition: JsonTask<Partitioning>,
                                            private val states: JsonTask<TransitionSystem<State>>)
    : SvgTask(outputName, partition, states) {

    override fun run() {
        val partition = partition.readJson()
        val transitions = states.readJson()
        writeImage(DeltaImage(partition, transitions, emptySet()))
    }

}