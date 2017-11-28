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

fun makeExperiments(partitioning: JsonTask<Partitioning>) = object {

    val All = object : JsonTask<TransitionSystem<State>>("ts.all.delta.json", type<TransitionSystem<State>>(), PWMA.Approximation, partitioning) {
        override fun run() {
            val model = PWMA.Approximation.readBio().toModelFactory()
            val partition = partitioning.readJson()

            runBlocking {
                writeJson(model.makeStateSpace(partition).system)
            }
        }

        //val svg = DeltaTransitionSystemSvgTask("ts.all.delta.svg", partitioning, this)
    }

    val States = object : JsonTask<TransitionSystem<State>>("ts.states.delta.json", type<TransitionSystem<State>>(), ModelFile, All) {
        override fun run() {
            val model = ModelFile.readBio().toModelFactory()
            val transitions = All.readJson()

            runBlocking {
                val admissible = model.checkStates(transitions)
                writeJson(admissible)
            }
        }

        val svg = DeltaTransitionSystemSvgTask("ts.states.delta.svg", partitioning, this)
    }

    val Transitions = object : JsonTask<TransitionSystem<State>>("ts.transitions.delta.json", type<TransitionSystem<State>>(), ModelFile, States) {
        override fun run() {
            val model = ModelFile.readBio().toModelFactory()
            val system = States.readJson()

            runBlocking {
                val admissible = model.checkTransitions(system)
                writeJson(admissible)
            }
        }

        val Svg = DeltaTransitionSystemSvgTask("ts.transitions.delta.svg", partitioning, this)
    }

    val TerminalComponents = object : JsonTask<List<State>>("terminal.delta.json", type<List<State>>(), Transitions) {
        override fun run() {
            val ts = Transitions.readJson()
            val terminal = ts.terminalComponents()
            writeJson(terminal.toList())
        }

        val Svg = DeltaTransitionSystemPropertySvgTask("terminal.delta.svg",
                partitioning, Transitions, this
        )
    }

    val InitialComponents = object : JsonTask<List<State>>("initial.delta.json", type<List<State>>(), Transitions) {
        override fun run() {
            val ts = Transitions.readJson()
            val terminal = ts.terminalComponents(false)
            writeJson(terminal.toList())
        }

        val Svg = DeltaTransitionSystemPropertySvgTask("initial.delta.svg",
                partitioning, Transitions, this
        )
    }
/*
    val Cycles = object : JsonTask<List<State>>("cycles.delta.json", type<List<State>>(), Transitions) {
        override fun run() {
            val ts = Transitions.readJson()
            val terminal = ts.states.filter { s ->
                s in ts.reachSet(ts.next(setOf(s)))
            }
            writeJson(terminal.toList())
        }

        val Svg = DeltaTransitionSystemPropertySvgTask("cycles.delta.svg",
                partitioning, Transitions, this
        )
    }*/
/*
    val BlenderExportTerminal = object : Task("terminal.delta.py", TerminalComponents) {
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
    }*/

}

object Delta {

    // https://www.bunnings.com.au/diy-advice/home-improvement/tiles/10-tile-patterns-you-need-to-know
    object Tile {
        object Herringbone : JsonTask<Partitioning>("partition.tile.json", type<Partitioning>(), ModelFile) {
            override fun run() {
                val model = ModelFile.readBio()
                val rSize = model.variables.map { (it.range.second - it.range.first) / 20 }.min() ?: 0.0
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

            object Svg : PartitionSvgTask("partition.tile.svg", Herringbone)
        }

        object BasketWeave : JsonTask<Partitioning>("partition.tile.json", type<Partitioning>(), ModelFile) {
            override fun run() {
                val model = ModelFile.readBio()
                val rSize = model.variables.map { (it.range.second - it.range.first) / 20 }.min() ?: 0.0
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

                    rectangle.weave().map { Partitioning.Item(it) }
                }

                writeJson(Partitioning(items))
            }

            object Svg : PartitionSvgTask("partition.tile.svg", BasketWeave)
        }

        object BigSmall : JsonTask<Partitioning>("partition.tile.json", type<Partitioning>(), ModelFile) {
            override fun run() {
                val model = ModelFile.readBio()
                val (xL, xH) = model.variables[0].range
                val (yL, yH) = model.variables[1].range
                val stepSize = maxOf(xL - xL, yH - yL) / 40.0

                val tX = buildSequence {
                    var t = xL
                    while (t < xH - 0.1) {
                        yield(t)
                        t += stepSize
                    }
                    yield(xH)
                }

                val tY = buildSequence {
                    var t = yL
                    while (t < yH - 0.1) {
                        yield(t)
                        t += stepSize
                    }
                    yield(yH)
                }

                fun thX(t: Double): Double = tX.map { it to Math.abs(t-it) }.minBy { it.second }!!.first
                fun thY(t: Double): Double = tY.map { it to Math.abs(t-it) }.minBy { it.second }!!.first

                val rectangles: List<Rectangle> = model.variables[2].thresholds.dropLast(1).zip(model.variables[2].thresholds.drop(1)).flatMap { (zL, zH) ->
                    buildSequence {
                        var x = xL
                        var shift = 0.0

                        while (thX(x) < xH) {
                            // 1 row of plain cubes
                            var y = yL
                            while (thY(y) < yH) {
                                yield(Rectangle(doubleArrayOf(thX(x), thX(x + stepSize), thY(y), thY(y + stepSize), zL, zH)))
                                y += stepSize
                            }

                            x += stepSize

                            if (thX(x) < xH) {
                                // 1 row of alternating cubes
                                var y2 = yL + shift
                                while (thY(y2) < yH) {
                                    yield(Rectangle(doubleArrayOf(thX(x), thX(x + 2 * stepSize), thY(y2), thY(y2 + 2 * stepSize), zL, zH)))
                                    y2 += 2 * stepSize
                                    if (thY(y2) < yH) {
                                        yield(Rectangle(doubleArrayOf(thX(x), thX(x + stepSize), thY(y2), thY(y2 + stepSize), zL, zH)))
                                        yield(Rectangle(doubleArrayOf(thX(x + stepSize), thX(x + 2 * stepSize), thY(y2), thY(y2 + stepSize), zL, zH)))
                                        y2 += stepSize
                                    }
                                }
                            }

                            x += 2 * stepSize

                            shift = if (shift == 0.0) stepSize else 0.0
                        }
                    }.toList()
                }

                writeJson(Partitioning(rectangles.map { Partitioning.Item(it) }))

            }

            object Svg : PartitionSvgTask("partition.tile.svg", BigSmall)
        }

        object BigSmallDiagonal : JsonTask<Partitioning>("partition.tile.json", type<Partitioning>(), ModelFile) {
            override fun run() {
                val model = ModelFile.readBio()
                val (xL, xH) = model.variables[0].range
                val (yL, yH) = model.variables[1].range
                val stepSize = maxOf(xL - xL, yH - yL) / 80.0

                val tX = buildSequence {
                    var t = xL
                    while (t < xH - 0.1) {
                        yield(t)
                        t += stepSize
                    }
                    yield(xH)
                }.toList()

                val tY = buildSequence {
                    var t = yL
                    while (t < yH - 0.1) {
                        yield(t)
                        t += stepSize
                    }
                    yield(yH)
                }.toList()

                fun thX(t: Double): Double = tX.map { it to Math.abs(t-it) }.minBy { it.second }!!.first
                fun thY(t: Double): Double = tY.map { it to Math.abs(t-it) }.minBy { it.second }!!.first

                val rectangles: List<Rectangle> = if (model.variables.size == 3) {
                    val (zL, zH) = model.variables[2].range
                    val tZ = buildSequence {
                        var t = zL
                        while (t < zH - stepSize) {
                            yield(t)
                            t += 2*stepSize // make z bit more coarse, since we don't have the two-one structure there
                        }
                        yield(zH)
                    }.toList()
                    var vShift = 0.0
                    tZ.dropLast(1).zip(tZ.drop(1)).flatMap { (zL, zH) ->
                        buildSequence<Rectangle> {
                            var x = xL - stepSize + vShift
                            var shift = 0.0

                            while (thX(x) < xH) {
                                var y = yL + shift + vShift
                                while (thY(y) < yH) {
                                    if (thY(y) < yH) {
                                        yield(Rectangle(doubleArrayOf(
                                                thX(x), thX(x + 2*stepSize),
                                                thY(y), thY(y + 2*stepSize),
                                                zL, zH
                                        )))
                                    }
                                    y += 2*stepSize
                                    if (thY(y) < yH && thX(x+stepSize) < xH) {
                                        yield(Rectangle(doubleArrayOf(
                                                thX(x+stepSize), thX(x + 2*stepSize),
                                                thY(y), thY(y + stepSize),
                                                zL, zH
                                        )))
                                    }
                                    y += 3*stepSize
                                }
                                x += stepSize
                                shift = when (shift) {
                                    0.0 -> -2*stepSize
                                    -2*stepSize -> stepSize
                                    stepSize -> -stepSize
                                    -stepSize -> 2*stepSize
                                    else -> 0.0
                                }
                            }
                            vShift = if (vShift == 0.0) -stepSize else 0.0
                        }.toList().filter { r -> r.degenrateDimensions == 0 }
                    }
                } else {
                    buildSequence<Rectangle> {
                        var x = xL - stepSize
                        var shift = 0.0

                        while (thX(x) < xH) {
                            var y = yL + 2*shift
                            while (thY(y) < yH) {
                                if (thY(y) < yH) {
                                    yield(Rectangle(doubleArrayOf(
                                            thX(x), thX(x + 2*stepSize),
                                            thY(y), thY(y + 2*2*stepSize)
                                    )))
                                }
                                y += 2*2*stepSize
                                if (thY(y) < yH && thX(x+stepSize) < xH) {
                                    yield(Rectangle(doubleArrayOf(
                                            thX(x+stepSize), thX(x + 2*stepSize),
                                            thY(y), thY(y + 2*stepSize)
                                    )))
                                }
                                y += 2*3*stepSize
                            }
                            x += stepSize
                            shift = when (shift) {
                                0.0 -> -2*stepSize
                                -2*stepSize -> stepSize
                                stepSize -> -stepSize
                                -stepSize -> 2*stepSize
                                else -> 0.0
                            }
                        }
                    }.toList().filter { r -> r.degenrateDimensions == 0 }
                }

                writeJson(Partitioning(rectangles.map { Partitioning.Item(it) }))

            }

            object Svg : PartitionSvgTask("partition.tile.svg", BigSmallDiagonal)
        }

        object Diagonal : JsonTask<Partitioning>("partition.tile.json", type<Partitioning>(), ModelFile) {
            override fun run() {
                val model = ModelFile.readBio()
                val tSize = model.variables.map { (it.range.second - it.range.first) / 80 }.min() ?: 0.0
                val t2Size = 3*tSize

                val (xL, xH) = model.variables[0].range
                val (yL, yH) = model.variables[1].range

                val tX = buildSequence {
                    var t = xL
                    while (t < xH - 0.1) {
                        yield(t)
                        t += tSize
                    }
                    yield(xH)
                }

                val tY = buildSequence {
                    var t = yL
                    while (t < yH - 0.1) {
                        yield(t)
                        t += tSize
                    }
                    yield(yH)
                }

                println(tX)
                println(tY)

                fun thX(t: Double): Double = tX.map { it to Math.abs(t-it) }.minBy { it.second }!!.first
                fun thY(t: Double): Double = tY.map { it to Math.abs(t-it) }.minBy { it.second }!!.first

                val rectangles = buildSequence {

                    // horizontal rectangles
                    var level = 0.0
                    do {
                        var shift = 0.0
                        do {
                            val r = Rectangle(doubleArrayOf(
                                    thX(xL + shift),
                                    thX(xL + shift + t2Size),
                                    thY(yL + level + shift),
                                    thY(yL + level + tSize + shift))
                            )
                            yield(r)
                            shift += tSize
                        } while (xL + shift < xH && yL + level + shift < yH)
                        level += 2 * t2Size
                    } while (yL + level < yH)
                    level = 2 * t2Size
                    do {
                        var shift = 0.0
                        do {
                            val r = Rectangle(doubleArrayOf(
                                    thX(xL + level + shift),
                                    thX(xL + level + shift + t2Size),
                                    thY(yL + shift),
                                    thY(yL + tSize + shift))
                            )
                            yield(r)
                            shift += tSize
                        } while (xL + shift < xH && yL + level + shift < yH)
                        level += 2 * t2Size
                    } while (xL + level < xH)

                    // vertical rectangles
                    level = tSize
                    do {
                        var shift = 0.0
                        do {
                            val r = Rectangle(doubleArrayOf(
                                    thX(xL + shift),
                                    thX(xL + shift + tSize),
                                    thY(yL + level + shift),
                                    thY(yL + level + shift + t2Size))
                            )
                            yield(r)
                            shift += tSize
                        } while (xL + shift < xH && yL + level + shift < yH)
                        level += 2 * t2Size
                    } while (yL + level < yH)
                    level = 2 * t2Size - tSize
                    do {
                        var shift = 0.0
                        do {
                            val r = Rectangle(doubleArrayOf(
                                    thX(xL + level + shift),
                                    thX(xL + level + shift + tSize),
                                    thY(yL + shift),
                                    thY(yL + t2Size + shift))
                            )
                            yield(r)
                            shift += tSize
                        } while (xL + shift < xH && yL + level + shift < yH)
                        level += 2 * t2Size
                    } while (xL + level < xH)
                }.toSet().map { Partitioning.Item(it) }

                writeJson(Partitioning(rectangles))
            }

            object Svg : PartitionSvgTask("partition.tile.svg", BasketWeave)
        }
    }

}