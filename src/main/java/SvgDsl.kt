
import com.github.sybila.ode.generator.rect.RectangleOdeModel
import com.github.sybila.ode.model.Parser
import dreal.DeltaModel
import dreal.State
import java.io.File

fun main(args: Array<String>) {
    val input = File("/Users/daemontus/Downloads/pol.bio")
    val f = File("/Users/daemontus/Downloads/test.svg")
    //val thresholds = listOf(-0.4, -0.24, -0.08, 0.08, 0.24, 0.4)
    val thresholdsX = (-40..40).map { it / 4.0 }
    val thresholdsY = (-20..20).map { it / 2.0 }
    //val thresholds = (0..50).map { it / 5.0 }
    val model = Parser().parse(input).let { m ->
        m.copy(variables = m.variables.mapIndexed { i, v ->
            v.copy(thresholds = if (i == 0) thresholdsX else thresholdsY)
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
    /*f.bufferedWriter().use { writer ->
        runBlocking {
            val abs = model.makeDeltaAbstraction(VanDerPolOscillator)
            val cycle = abs.states.filter {
                println("Check $it")
                val successors = abs.transitions[it]
                it in abs.forward(successors?.toSet() ?: emptySet())
            }.toSet()
            //val reach = abs.forward(setOf(State.Transition(50, 51)))
            //val reach = abs.forward(setOf(State.Transition(1, 0)))
            //val one = abs.backward(setOf(State.Interior(173)))
            //val two = abs.backward(setOf(State.Interior(1229)))
            DeltaImage(model, abs, cycle).toSvgImage().normalize(1000.0).writeTo(writer)
        }
    }*/
}

fun DeltaModel.invert(set: Set<State>): Set<State> = (states - set).toSet()

fun DeltaModel.next(from: Set<State>, time: Boolean = true): Set<State> {
    val ts = if (time) transitions else transitions.flatMap { (s, succ) -> succ.map { it to s } }.groupBy({ it.first }, { it.second })
    return from.flatMap { ts[it] ?: emptyList() }.toSet()
}

fun DeltaModel.reach(from: Set<State>, time: Boolean = true): Set<State> {
    val ts = if (time) transitions else transitions.flatMap { (s, succ) -> succ.map { it to s } }.groupBy({ it.first }, { it.second })
    var iteration = from
    do {
        val old = iteration
        iteration += iteration.flatMap { ts[it] ?: emptyList() }.toSet()
    } while (old != iteration)
    return iteration
}

fun DeltaModel.terminal(time: Boolean = true): Set<State> {
    val terminal = HashSet<State>()

    fun explore(states: Set<State>) {
        println("Iter: ${states.size}")
        val co = this.states - states
        val pivot = states.iterator().next()
        val F = reach(setOf(pivot), time) - co
        val B = reach(setOf(pivot), !time) - (this.states - F)
        val F_minus_B = F - B
        if (F_minus_B.isEmpty()) terminal.addAll(F) else {
            println("F_minus_B")
            explore(F_minus_B)
        }
        val BB = reach(F, !time) - co
        val V_minus_BB = states - BB
        println("BB")
        if (V_minus_BB.isNotEmpty()) explore(V_minus_BB)
    }

    explore(this.states.toSet())
    return terminal
}

fun RectangleOdeModel.next(input: Set<Int>, time: Boolean = true): Set<Int>
    = input.flatMap{ it.successors(time).asSequence().map { it.target }.toList() }.toSet()

fun RectangleOdeModel.reach(input: Set<Int>, time: Boolean = true): Set<Int> {
    var iteration = input
    do {
        val old = iteration
        iteration += next(iteration, time)
    } while (old.toList().sorted() != iteration.toList().sorted())
    return iteration
}

fun RectangleOdeModel.invert(input: Set<Int>): Set<Int> = (0 until stateCount).toSet() - input