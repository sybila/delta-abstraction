
import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.Parser
import dreal.*
import kotlinx.coroutines.experimental.runBlocking
import svg.DeltaImage
import java.io.File

fun main(args: Array<String>) {
    val input = File("/Users/daemontus/Downloads/test.bio")
    val f = File("/Users/daemontus/Downloads/test.svg")
    //val thresholds = (-10..10).map { it / 2.0 }
    val thresholds = (0..30).map { it / 3.0 }
    val model = Parser().parse(input).let { m ->
        m.copy(variables = m.variables.map { v ->
            v.copy(thresholds = thresholds)
        })
    }

    /*val ts = RectangleOdeModel(model, createSelfLoops = true)
    ts.run {
        val stable = (0 until stateCount).filter {
            println("Check stable $it")
            it in invert(backwards(invert(backwards(setOf(it)))))
        }.toSet()
        val c1: Int = stable.first()
        val c2: Int = stable.first { c1 !in backwards(setOf(it)) }
        val r1 = backwards(setOf(c1))
        val r2 = backwards(setOf(c2))
        val and = r1 - (r1 - r2)
        f.bufferedWriter().use { writer ->
            PwmaImage(model, ts, mapOf(
                    "#ff0000" to stable,
                    "#00ff00" to r1,
                    "#0000ff" to r2,
                    "#00ffff" to and
                    )).toSvgImage().normalize(1000.0).writeTo(writer)
        }
    }*/
    /*val delta = DeltaModel(listOf(
            Interior(0),
            Interior(10),
            Interior(200),
            Interior(280),
            State.Transition(10,11),
            State.Transition(11,10),
            State.Transition(10,9),
            State.Transition(10,50),
            State.Transition(50,10),
            State.Transition(10, null),
            State.Transition(null, 10),
            State.Transition(null, 0),
            State.Transition(0, null),
            State.Transition(null, 1599),
            State.Transition(1599, null),
            State.Transition(null, 39),
            State.Transition(39, null),
            State.Transition(null, 1560),
            State.Transition(1560, null)
    ), mapOf(
            State.Transition(null, 10) to listOf(State.Transition(10, 11), State.Transition(10, 50)),
            State.Transition(11, 10) to listOf(State.Transition(10, null), State.Interior(10))
    ))*/
    f.bufferedWriter().use { writer ->
        runBlocking {
            val abs = model.makeDeltaAbstraction(G1Sswitch)
            val reach = abs.forward(setOf(State.Interior(FIND)))
            DeltaImage(model, abs, reach).toSvgImage().normalize(1000.0).writeTo(writer)
        }
    }
}

fun DeltaModel.forward(from: Set<State>): Set<State> {
    var iteration = from
    do {
        val old = iteration
        iteration += iteration.flatMap { transitions[it] ?: emptyList() }.toSet()
        println(iteration)
    } while (old != iteration)
    return iteration
}

fun RectangleOdeModel.backwards(input: Set<Int>): Set<Int> {
    var iteration = input
    do {
        val old = iteration
        iteration += iteration.flatMap { it.successors(false).asSequence().map { it.target }.toList() }.toSet()
    } while (old.toList().sorted() != iteration.toList().sorted())
    return iteration
}

fun RectangleOdeModel.invert(input: Set<Int>): Set<Int> = (0 until stateCount).toSet() - input