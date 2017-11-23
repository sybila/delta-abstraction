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

    override fun toString(): String = this.javaClass.name//.removePrefix("dreal.project.")
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
        val dimen = partition.items.first().bounds.dimensions
        if (dimen == 2) {
            writeSvg(SvgImage(partition.items.map { it.bounds.toSvgRectangle() }, 0.0))
        } else if (dimen == 3) {
            val thresholds = partition.items.asSequence().flatMap {
                sequenceOf(it.bounds.bound(2, false), it.bounds.bound(2, true))
            }.toSet()
            thresholds.forEach { t ->
                val newPartition = partition.items.map { it.bounds }.filter { it.contains(2, t) }.map { it.project(2) }
                Config  .projectFile("${output.name}_$t.svg")
                        .writeText(
                                SvgImage(newPartition.map { it.toSvgRectangle() }, 0.0)
                                    .normalize(Config.targetWidth)
                                    .compileSvg()
                        )
            }
        }
    }

}

class DeltaTransitionSystemSvgTask(outputName: String,
                                            private val partition: JsonTask<Partitioning>,
                                            private val states: JsonTask<TransitionSystem<State>>)
    : SvgTask(outputName, partition, states) {

    override fun run() {
        val partition = partition.readJson()
        val transitions = states.readJson()
        val dimen = partition.items.first().bounds.dimensions
        if (dimen == 2) {
            writeImage(DeltaImage(partition, transitions, emptySet()))
        } else if (dimen == 3) {
            val thresholds = partition.items.asSequence().flatMap {
                sequenceOf(it.bounds.bound(2, false), it.bounds.bound(2, true))
            }.toSet()
            thresholds.forEach { t ->
                val newPartition = Partitioning(partition.items.map { it.bounds }.filter { it.contains(2, t) }.map { Partitioning.Item(it.project(2)) })
                val newStates = transitions.states.map {
                    if (!it.contains(2, t)) null else it.project(2)
                }
                val newStateList = newStates.filterNotNull()
                val newEdges = transitions.edges.mapNotNull { (s,t) ->
                    val start = newStates[s]
                    val target = newStates[t]
                    if (start == null || target == null) null else {
                        newStateList.indexOf(start) to newStateList.indexOf(target)
                    }
                }
                Config  .projectFile("${output.name}_$t.svg")
                        .writeText(
                                DeltaImage(newPartition, TransitionSystem(newStateList, newEdges), emptySet())
                                        .toSvgImage().normalize(Config.targetWidth).compileSvg()
                        )
            }
        }
    }

}

class DeltaTransitionSystemPropertySvgTask(outputName: String,
                                            private val partition: JsonTask<Partitioning>,
                                            private val states: JsonTask<TransitionSystem<State>>,
                                            private val property: JsonTask<List<State>>)
    : SvgTask(outputName, partition, states, property) {

    override fun run() {
        val partition = partition.readJson()
        val transitions = states.readJson()
        val prop = property.readJson()
        val dimen = partition.items.first().bounds.dimensions
        if (dimen == 2) {
            writeImage(DeltaImage(partition, transitions, prop.toSet()))
        } else if (dimen == 3) {
            val thresholds = partition.items.asSequence().flatMap {
                sequenceOf(it.bounds.bound(2, false), it.bounds.bound(2, true))
            }.toSet()
            thresholds.forEach { t ->
                val newPartition = Partitioning(partition.items.map { it.bounds }.filter { it.contains(2, t) }.map { Partitioning.Item(it.project(2)) })
                val newStates = transitions.states.map {
                    if (!it.contains(2, t)) null else it.project(2)
                }
                val newProp = prop.filter { it.contains(2, t) }.map { it.project(2) }
                val newStateList = newStates.filterNotNull()
                val newEdges = transitions.edges.mapNotNull { (s,t) ->
                    val start = newStates[s]
                    val target = newStates[t]
                    if (start == null || target == null) null else {
                        newStateList.indexOf(start) to newStateList.indexOf(target)
                    }
                }
                Config  .projectFile(t.toString()+"_"+output.name)
                        .writeText(
                                DeltaImage(newPartition, TransitionSystem(newStateList, newEdges), newProp.toSet())
                                        .toSvgImage().normalize(Config.targetWidth).compileSvg()
                        )
            }
        }
    }

}