package dreal

fun <T: Any> TransitionSystem<T>.invert(): TransitionSystem<T> = this.copy(edges = edges.map { it.second to it.first })

fun <T: Any> TransitionSystem<T>.terminalComponents(time: Boolean = true): Set<T> {
    val f = this.edges.groupBy({ states[it.first] }, { states[it.second] })
    val b = this.edges.groupBy({ states[it.second] }, { states[it.first] })
    val fwd = if (time) f else b
    val bwd = if (time) b else f

    val result = HashSet<T>()
    fun search(V: Set<T>) {
        val pivot = V.toList().get((Math.random() * V.size).toInt())

        val F = fwd.run { reachSet(setOf(pivot), V) }
        val B = bwd.run { reachSet(setOf(pivot), F) }
        val BB = bwd.run { reachSet(F, V) }

        val F_minus_B = F - B
        val V_minus_BB = V - BB

        if (F_minus_B.isEmpty()) {
            result.addAll(F)
        } else {
            search(F_minus_B)
        }

        if (V_minus_BB.isNotEmpty()) search(V_minus_BB)
    }

    search(states.toSet())

    return result
}

fun <T: Any> TransitionSystem<T>.reachSet(from: Set<T>, time: Boolean = true): Set<T> {
    val ts = if (time) {
        this.edges.groupBy({ states[it.first] }, { states[it.second] })
    } else {
        this.edges.groupBy({ states[it.second] }, { states[it.first] })
    }

    return ts.reachSet(from)
}

fun <T: Any> TransitionSystem<T>.reachAllSet(from: Set<T>, time: Boolean = true): Set<T> {
    val futureTS = this.edges.groupBy({ states[it.first] }, { states[it.second] })
    val pastTS = this.edges.groupBy({ states[it.second] }, { states[it.first] })
    val (front, back) = if (time) (futureTS to pastTS) else (pastTS to futureTS)

    var iteration = from
    do {
        val old = iteration
        val check = iteration.asSequence().flatMap { front[it]?.asSequence() ?: emptySequence() }.toSet()
        val update = check.asSequence().filter { back[it]?.all { it in iteration } ?: true }.toSet()
        iteration += update
    } while (iteration != old)

    return iteration
}

fun <T: Any> TransitionSystem<T>.next(from: Set<T>, time: Boolean = true): Set<T> {
    val ts = if (time) {
        this.edges.groupBy({ states[it.first] }, { states[it.second] })
    } else {
        this.edges.groupBy({ states[it.second] }, { states[it.first] })
    }

    return from.asSequence().flatMap { ts[it]?.asSequence() ?: emptySequence() }.toSet()
}
/*
fun <T: Any> TransitionSystem<T>.nextNoZ(from: Set<T>, time: Boolean = true): Set<T> {
    val ts = if (time) {
        this.edges.groupBy({ states[it.first] }, { states[it.second] })
    } else {
        this.edges.groupBy({ states[it.second] }, { states[it.first] })
    }

    return from.asSequence().flatMap { ts[it]?.asSequence() ?: emptySequence() }.filter {
        if (it !is State.Transition) true else it.from.getFacetIntersection(it.to)!!.dimension != 2
    }.toSet()
}*/

fun <T: Any> Map<T, List<T>>.reachSet(data: Set<T>, bound: Set<T>? = null): Set<T> {
    var iteration = data
    do {
        val old = iteration
        iteration += iteration.asSequence().flatMap { this[it]?.asSequence() ?: emptySequence() }.toSet()
        if (bound != null) {
            iteration = iteration.intersect(bound)
        }
    } while (iteration != old)

    return iteration
}
