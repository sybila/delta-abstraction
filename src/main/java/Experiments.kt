
import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.Parser
import com.github.sybila.ode.model.computeApproximation
import com.github.sybila.ode.model.toBio
import com.google.gson.GsonBuilder
import dreal.filterAdmissibleStates
import dreal.makeStateSpace
import dreal.toModelFactory
import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.async
import kotlinx.coroutines.experimental.runBlocking
import svg.PwmaImage
import java.io.File
/*
object StateSerializer : JsonSerializer<State>, JsonDeserializer<State> {

    override fun serialize(src: State, typeOfSrc: Type, context: JsonSerializationContext): JsonElement {
        when (src)
    }

    override fun deserialize(json: JsonElement, typeOfT: Type, context: JsonDeserializationContext): State {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

}
*/
val json = GsonBuilder().setPrettyPrinting()/*.registerTypeAdapter(State::class.java, StateSerializer)*/.create()!!

fun makePwmaAbstraction(suffix: String) {
    val model = Parser()
            .parse(File(projectRoot, "model.$suffix.bio"))
            .computeApproximation(cutToRange = true, fast = false)

    val modelCopy = model.copy(variables = model.variables.mapIndexed { index, variable ->
        if (index != 1) variable else {
            val (l, h) = variable.range
            val count = variable.varPoints!!.second
            val step = (h - l) / count
            variable.copy(
                    thresholds = (0 until count).map { l + it * step } + listOf(h)
            )
        }
    })

    File(projectRoot, "model.pwma.$suffix.bio")
            .writeText(modelCopy.toBio())
}

fun makePwmaPartition(suffix: String) {
    val model = Parser()
            .parse(File(projectRoot, "model.pwma.$suffix.bio"))

    File(projectRoot, "partition.pwma.$suffix.json")
            .writeText(json.toJson(model.exportPartitioning()))
}

fun makeTerminalComponents(suffix: String) {
    val model = Parser()
            .parse(File(projectRoot, "model.pwma.$suffix.bio"))

    val ts = RectangleOdeModel(model, true)

    runBlocking {
        val terminal = (0 until ts.stateCount).map { async(CommonPool) {
            if (it % 100 == 0) println(it)
            it.takeIf { it in ts.invert(ts.reach(ts.invert(ts.reach(setOf(it), false)), false)) }
        } }.mapNotNull { it.await() }

        val initial = (0 until ts.stateCount).map { async(CommonPool) {
            if (it % 100 == 0) println(it)
            it.takeIf { it in ts.invert(ts.reach(ts.invert(ts.reach(setOf(it), true)), true)) }
        } }.mapNotNull { it.await() }

        val cycle = (0 until ts.stateCount).map { async(CommonPool) {
            if (it % 100 == 0) println(it)
            it.takeIf { it in ts.reach(ts.next(setOf(it)), true) }
        } }.mapNotNull { it.await() }

        File(projectRoot, "terminal.pwma.$suffix.json")
                .writeText(json.toJson(terminal))

        File(projectRoot, "initial.pwma.$suffix.json")
                .writeText(json.toJson(initial))

        File(projectRoot, "cycle.pwma.$suffix.json")
                .writeText(json.toJson(cycle))
    }

}

fun makePwmaSvg(suffix: String, targetWidth: Double) {
    val model = Parser()
            .parse(File(projectRoot, "model.pwma.$suffix.bio"))
    val ts = RectangleOdeModel(model, true)

    val terminal = json.fromJson<List<Int>>(    File(projectRoot, "terminal.pwma.$suffix.json").readText(),
                                                List::class.java
    ).toSet()

    val initial = json.fromJson<List<Int>>( File(projectRoot, "initial.pwma.$suffix.json").readText(),
                                            List::class.java
    ).toSet()

    val cycle = json.fromJson<List<Int>>(   File(projectRoot, "cycle.pwma.$suffix.json").readText(),
                                            List::class.java
    ).toSet()

    val imgPlain = PwmaImage(model, ts, emptyMap())
    val imgTerminal = PwmaImage(model, ts, mapOf("#aaaaff" to terminal))
    val imgInitial = PwmaImage(model, ts, mapOf("#ffaaaa" to initial))
    val imgCycle = PwmaImage(model, ts, mapOf("#aaffaa" to cycle))
    val imgAll = PwmaImage(model, ts, mapOf("#aaffaa" to cycle, "#ffaaaa" to initial, "#aaaaff" to terminal))
    File(projectRoot, "ts.pwma.$suffix.svg")
            .writeText(imgPlain.toSvgImage().normalize(targetWidth).compileSvg())
    File(projectRoot, "terminal.pwma.$suffix.svg")
            .writeText(imgTerminal.toSvgImage().normalize(targetWidth).compileSvg())
    File(projectRoot, "initial.pwma.$suffix.svg")
            .writeText(imgInitial.toSvgImage().normalize(targetWidth).compileSvg())
    File(projectRoot, "cycle.pwma.$suffix.svg")
            .writeText(imgCycle.toSvgImage().normalize(targetWidth).compileSvg())
    File(projectRoot, "all.pwma.$suffix.svg")
            .writeText(imgAll.toSvgImage().normalize(targetWidth).compileSvg())
}

suspend fun makeDeltaTransitions(tMax: Double, suffix: String, targetWidth: Double, partition: String) {
    val ode = Parser()
            .parse(File(projectRoot, "model.$suffix.bio"))

    val partitioning = json.fromJson(File(projectRoot, "partition.$partition.$suffix.json").readText(), Partitioning::class.java)

    val model = ode.toModelFactory()
            .makeStateSpace(partitioning.rectangles)
            .filterAdmissibleStates(tMax)

    val m = model

    runBlocking {
        val terminal = m.states.map { async(CommonPool) {
            it.takeIf { it in m.invert(m.reach(m.invert(m.reach(setOf(it), false)), false)) }
        } }.mapNotNull { it.await() }.toSet()

        val initial = m.states.map { async(CommonPool) {
            it.takeIf { it in m.invert(m.reach(m.invert(m.reach(setOf(it), true)), true)) }
        } }.mapNotNull { it.await() }.toSet()

        val cycle = m.states.map { async(CommonPool) {
            it.takeIf { it in m.reach(m.next(setOf(it)), true) }
        } }.mapNotNull { it.await() }.toSet()

        /*File(projectRoot, "terminal.pwma.$suffix.json")
                .writeText(json.toJson(terminal))

        File(projectRoot, "initial.pwma.$suffix.json")
                .writeText(json.toJson(initial))

        File(projectRoot, "cycle.pwma.$suffix.json")
                .writeText(json.toJson(cycle))*/
        /*val imgPlain = DeltaImage(model, emptySet())
        val imgTerminal = DeltaImage(model, terminal)
        val imgInitial = DeltaImage(model, initial)
        val imgCycle = DeltaImage(model, cycle)
        File(projectRoot, "ts.delta.$suffix.svg")
                .writeText(imgPlain.toSvgImage().normalize(targetWidth).compileSvg())
        File(projectRoot, "terminal.delta.$suffix.svg")
                .writeText(imgTerminal.toSvgImage().normalize(targetWidth).compileSvg())
        File(projectRoot, "initial.delta.$suffix.svg")
                .writeText(imgInitial.toSvgImage().normalize(targetWidth).compileSvg())
        File(projectRoot, "cycle.delta.$suffix.svg")
                .writeText(imgCycle.toSvgImage().normalize(targetWidth).compileSvg())*/
        println("Terminal ${terminal.size} / ${m.states.size}")
        println("Initial ${initial.size} / ${m.states.size}")
        println("Cycle ${cycle.size} / ${m.states.size}")
        println("Terminal: $terminal")
        println("Initial: $initial")
        println("Cycle: $cycle")
        //File(projectRoot, "all.pwma.$suffix.svg")
        //        .writeText(imgAll.toSvgImage().normalize(targetWidth).compileSvg())
    }

    //File(projectRoot, "ts.delta.$suffix.svg")
    //        .writeText(DeltaImage(model, emptySet()).toSvgImage().normalize(targetWidth).compileSvg())

}

val projectRoot = File("chua/")

fun main(args: Array<String>) {
    runBlocking {
        val suffix = "10x10x10"
        val targetWidth = 1000.0
        val tMax = 0.1
/*
        makePwmaAbstraction(suffix)
        makePwmaPartition(suffix)
        makeTerminalComponents(suffix)
        makePwmaSvg(suffix, targetWidth)
*/
        makePwmaAbstraction(suffix)
        makePwmaPartition(suffix)
        makeDeltaTransitions(tMax, suffix, targetWidth, "pwma")
    }
}