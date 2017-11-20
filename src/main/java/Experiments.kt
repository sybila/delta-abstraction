/*
import dreal.project.DeltaTransitionSystemSvg
import dreal.project.RectangularPartitioningSvg
import dreal.project.RectangularTransitionSystemSvg
import dreal.project.delta.DeltaTransitionSystemTask
import dreal.project.pwma.ApproximationTask
import dreal.project.pwma.RectangularTransitionSystemTask
import dreal.project.pwma.RectangularPartitioningTask
import dreal.project.pwma.RectangularTerminalComponentsSvg
import kotlinx.coroutines.experimental.runBlocking
*/
/*
private class SerializedState(
        val tag: String,
        val r1: Rectangle?,
        val r2: Rectangle?
)

private object StateSerializer : JsonSerializer<State>, JsonDeserializer<State> {

    override fun serialize(src: State, typeOfSrc: Type, context: JsonSerializationContext): JsonElement {
        return when (src) {
            is State.Exterior -> context.serialize(SerializedState("exterior", null, null))
            is State.Interior -> context.serialize(SerializedState("interior", src.rectangle, null))
            is State.Transition -> context.serialize(SerializedState("transition", src.from, src.to))
        }
    }

    override fun deserialize(json: JsonElement, typeOfT: Type, context: JsonDeserializationContext): State {
        val serialized = context.deserialize<SerializedState>(json, SerializedState::class.java)
        return when (serialized.tag) {
            "exterior" -> State.Exterior
            "interior" -> State.Interior(serialized.r1!!)
            "transition" -> State.Transition(serialized.r1!!, serialized.r2!!)
            else -> error("Unknown tag ${serialized.tag}")
        }
    }

}

val json = GsonBuilder().setPrettyPrinting().registerTypeAdapter(State::class.java, StateSerializer).create()!!

fun makeSplitPartition(suffix: String, tMax: Double, precision: Double) {
    val model = Parser()
            .parse(File(projectRoot, "model.$suffix.bio"))

    runBlocking {
        File(projectRoot, "partition.split.$suffix.json")
                .writeText(json.toJson(model.makePartitioning(tMax, precision)))
    }
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
*/
/*
suspend fun makeDeltaTransitions(tMax: Double, suffix: String, targetWidth: Double, partition: String) {
    val ode = Parser()
            .parse(File(projectRoot, "model.$suffix.bio"))

    val partitioning = json.fromJson(File(projectRoot, "partition.$partition.$suffix.json").readText(), Partitioning::class.java)

    val model = ode.toModelFactory()
            .makeStateSpace(partitioning)
            .filterAdmissibleStates(tMax)
            .reduction()

    File(projectRoot, "ts.delta.json")
            .writeText(json.toJson(model.system.toList()))

    val imgPlain = DeltaImage(model, emptySet())
    File(projectRoot, "ts.delta.svg")
            .writeText(imgPlain.toSvgImage().normalize(targetWidth).compileSvg())

    /*
    val m = model

    runBlocking {
        var k = 0
        val initial = m.terminal(false)
        val terminal = m.states.map { async(CommonPool) {
            it.takeIf { it in m.invert(m.reach(m.invert(m.reach(setOf(it), false)), false)) }
        } }.mapNotNull { it.await().also {
            k += 1
            println("T: $k / ${m.states.size}")
        } }.toSet()
/*
        k = 0
        val initial = m.states.map { async(CommonPool) {
            it.takeIf { it in m.invert(m.reach(m.invert(m.reach(setOf(it), true)), true)) }
        } }.mapNotNull { it.await().also {
            k += 1
            println("I: $k / ${m.states.size}")
        } }.toSet()

        k = 0
        val cycle = m.states.map { async(CommonPool) {
            it.takeIf { it in m.reach(m.next(setOf(it)), true) }
        } }.mapNotNull { it.await().also {
            k += 1
            println("C: $k / ${m.states.size}")
        } }.toSet()*/

        /*File(projectRoot, "terminal.pwma.$suffix.json")
                .writeText(json.toJson(terminal))

        File(projectRoot, "initial.pwma.$suffix.json")
                .writeText(json.toJson(initial))

        File(projectRoot, "cycle.pwma.$suffix.json")
                .writeText(json.toJson(cycle))*/
        val imgTerminal = DeltaImage(model, terminal)
        val imgInitial = DeltaImage(model, initial)
        //val imgCycle = DeltaImage(model, cycle)
        File(projectRoot, "terminal.delta.$suffix.svg")
                .writeText(imgTerminal.toSvgImage().normalize(targetWidth).compileSvg())
        File(projectRoot, "initial.delta.$suffix.svg")
                .writeText(imgInitial.toSvgImage().normalize(targetWidth).compileSvg())
        /*File(projectRoot, "cycle.delta.$suffix.svg")
                .writeText(imgCycle.toSvgImage().normalize(targetWidth).compileSvg())*/
        println("Terminal ${terminal.size} / ${m.states.size}")
        println("Initial ${initial.size} / ${m.states.size}")
        //println("Cycle ${cycle.size} / ${m.states.size}")
        /*println("Terminal: $terminal")
        println("Initial: $initial")
        println("Cycle: $cycle")*/
        //File(projectRoot, "all.pwma.$suffix.svg")
        //        .writeText(imgAll.toSvgImage().normalize(targetWidth).compileSvg())

        var iter = model.states.toSet()
        do {
            val old = iter
            iter = model.next(iter)
        } while (old != iter)

        val imgFix = DeltaImage(model, iter)
        File(projectRoot, "fix.delta.$suffix.svg")
                .writeText(imgFix.toSvgImage().normalize(targetWidth).compileSvg())
        println("Fix ${iter.size} / ${m.states.size }")
    }

    //File(projectRoot, "ts.delta.$suffix.svg")
    //        .writeText(DeltaImage(model, emptySet()).toSvgImage().normalize(targetWidth).compileSvg())
*/
}

fun investigate(targetWidth: Double) {
    val system = json.fromJson<List<Pair<State, List<State>>>>(File(projectRoot, "ts.delta.json").bufferedReader(), List::class.java)

    val ode = Parser().parse(File(projectRoot, "model.30x40.bio"))

    val model = DeltaModel()

    val t = model.system.entries.map { it.key to it.value.size }
    val maxSize = t.maxBy { it.second }!!.second
    val max = t.filter { it.second == maxSize }.map { it.first }.toSet()

    val img = DeltaImage(model, max)
    File(projectRoot, "prop.delta.svg")
            .writeText(img.toSvgImage().normalize(targetWidth).compileSvg())
}

val projectRoot = File("pol/")

*/

/*
fun main(args: Array<String>) {
    runBlocking {
        val suffix = "40x30"
        val targetWidth = 1000.0
        val tMax = 0.1
        /*
        ApproximationTask.output.delete()
        RectangularPartitioningTask.output.delete()
        RectangularPartitioningSvg.output.delete()
        RectangularTransitionSystemTask.output.delete()
        */
        ApproximationTask.execute()
        RectangularPartitioningTask.execute()
        RectangularPartitioningSvg.execute()
        RectangularTransitionSystemTask.execute()
        RectangularTransitionSystemSvg.execute()
        RectangularTerminalComponentsSvg.execute()

        DeltaTransitionSystemTask.execute()
        DeltaTransitionSystemSvg.execute()
    }
}*/