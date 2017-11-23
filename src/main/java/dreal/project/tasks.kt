package dreal.project

import com.github.sybila.ode.generator.NodeEncoder
import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.computeApproximation
import dreal.*
import kotlinx.coroutines.experimental.runBlocking
import svg.PwmaImage
import kotlin.coroutines.experimental.buildSequence

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

    object Tile {
        object Partition : JsonTask<Partitioning>("partition.tile.json", type<Partitioning>(), ModelFile) {
            override fun run() {
                val model = ModelFile.readBio()
                val rSize = model.variables.map { (it.range.second - it.range.first) / 30 }.min() ?: 0.0
                val newVars = model.variables.map { v ->
                    val t = buildSequence {
                        yield(v.range.first)
                        var k = v.range.first + rSize
                        while (k < v.range.second) {
                            yield(k)
                            k += rSize
                        }
                        yield(v.range.second)
                    }.toList()
                    v.copy(thresholds = t)
                }
                val newModel = model.copy(variables = newVars)

                val encoder = NodeEncoder(newModel)
                val ts = RectangleOdeModel(newModel, true)

                val items = (0 until ts.stateCount).flatMap { s ->
                    val rectangle = Rectangle(newVars.indices.flatMap { i ->
                        val t = newVars[i].thresholds
                        listOf(t[encoder.lowerThreshold(s, i)], t[encoder.upperThreshold(s, i)])
                    }.toDoubleArray())

                    val splitDimension = encoder.decodeNode(s).map { it % encoder.dimensions }.sum() % encoder.dimensions

                    val (l, h) = rectangle.split(splitDimension)
                    listOf(Partitioning.Item(l), Partitioning.Item(h))
                }

                writeJson(Partitioning(items))
            }

            object Svg : PartitionSvgTask("partition.tile.svg", Partition)
        }
    }

    object Rectangular {

        object All : JsonTask<TransitionSystem<State>>("ts.all.delta.rect.json", type<TransitionSystem<State>>(), PWMA.Approximation, Tile.Partition) {
            override fun run() {
                val model = PWMA.Approximation.readBio().toModelFactory()
                val partition = PWMA.Partition.readJson()

                runBlocking {
                    writeJson(model.makeStateSpace(partition).system)
                }
            }

            object Svg : DeltaTransitionSystemSvgTask("ts.all.delta.rect.svg", Tile.Partition, All)
        }

        object States : JsonTask<TransitionSystem<State>>("ts.states.delta.rect.json", type<TransitionSystem<State>>(), ModelFile, All) {
            override fun run() {
                val model = ModelFile.readBio().toModelFactory()
                val transitions = All.readJson()

                runBlocking {
                    val admissible = model.checkStates(transitions)
                    writeJson(admissible)
                }
            }

            object Svg : DeltaTransitionSystemSvgTask("ts.states.delta.rect.svg", Tile.Partition, States)
        }

        object Transitions : JsonTask<TransitionSystem<State>>("ts.transitions.delta.rect.json", type<TransitionSystem<State>>(), ModelFile, States) {
            override fun run() {
                val model = ModelFile.readBio().toModelFactory()
                val system = States.readJson()

                runBlocking {
                    val admissible = model.checkTransitions(system)
                    writeJson(admissible)
                }
            }

            object Svg : DeltaTransitionSystemSvgTask("ts.transitions.delta.rect.svg", Tile.Partition, Transitions)
        }

        object TerminalComponents : JsonTask<List<State>>("terminal.delta.rect.json", type<List<State>>(), Transitions) {
            override fun run() {
                val ts = Transitions.readJson()
                val terminal = ts.terminalComponents()
                writeJson(terminal.toList())
            }

            object Svg : DeltaTransitionSystemPropertySvgTask("terminal.delta.rect.svg",
                    Tile.Partition, Transitions, TerminalComponents
            )
        }

        object InitialComponents : JsonTask<List<State>>("initial.delta.rect.json", type<List<State>>(), Transitions) {
            override fun run() {
                val ts = Transitions.readJson()
                val terminal = ts.terminalComponents(false)
                writeJson(terminal.toList())
            }

            object Svg : DeltaTransitionSystemPropertySvgTask("initial.delta.rect.svg",
                    Tile.Partition, Transitions, InitialComponents
            )
        }

        object Cycles : JsonTask<List<State>>("cycles.delta.rect.json", type<List<State>>(), Transitions) {
            override fun run() {
                val ts = Transitions.readJson()
                val terminal = ts.states.filter { s ->
                    s in ts.reachSet(ts.next(setOf(s)))
                }
                writeJson(terminal.toList())
            }

            object Svg : DeltaTransitionSystemPropertySvgTask("cycles.delta.rect.svg",
                    Tile.Partition, Transitions, Cycles
            )
        }

        object BlenderExportTerminal : Task("terminal.delta.rect.py") {
            override fun run() {
                val terminal = TerminalComponents.readJson()
                val rectangles = terminal.mapNotNull { when (it) {
                    is State.Exterior -> null
                    is State.Interior -> it.rectangle
                    is State.Transition -> it.to
                } }.toSet()

                val commands = rectangles.map { r ->
                    val location = DoubleArray(3) { i ->
                        (r.bound(i, false) + r.bound(i, true)) / 2
                    }.joinToString(separator = ",")
                    val proportions = DoubleArray(3) { i ->
                        val size = r.bound(i, true) - r.bound(i, false)
                        size/2  // default cube has size 2
                    }.joinToString(separator = ",")
                    //println("Rectangle $r at $location with resize $proportions")
                    """
                        bpy.ops.mesh.primitive_cube_add(location=($location))
                        bpy.ops.transform.resize(value=($proportions))
                        bpy.context.active_object.data.materials.append(solid)
                    """

                }

                val script = """
                import bpy

                solid = bpy.data.materials.get("solid")
                if solid is None:
                        solid = bpy.data.materials.new(name = "solid")
                        solid.diffuse_color = (0.8, 0.8, 1.0)
                        solid.specular_intensity = 0.0
                        solid.emit = 0.5

                wire = bpy.data.materials.get("wire")
                if wire is None:
                        wire = bpy.data.materials.new(name = "wire")
                        wire.type = 'WIRE'
                        wire.diffuse_color = (0.0, 0.0, 0.0)
                        wire.specular_intensity = 0.0
                        wire.offset_z = 0.01
                        wire.use_transparency = True
                        wire.emit = 0.5

                ${commands.joinToString(separator = "\n")}
                """
                output.writeText(script)
            }
        }

    }

}