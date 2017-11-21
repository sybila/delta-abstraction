package dreal.project

fun <T: Any> TransitionSystem<T>.invert(): TransitionSystem<T> = this.copy(edges = edges.map { it.second to it.first })

fun <T: Any> TransitionSystem<T>.terminalComponents(): Set<T> {
    val fwd = this.edges.groupBy({ states[it.first] }, { states[it.second] })
    val bwd = this.edges.groupBy({ states[it.second] }, { states[it.first] })

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

fun <T: Any> TransitionSystem<T>.next(from: Set<T>, time: Boolean = true): Set<T> {
    val ts = if (time) {
        this.edges.groupBy({ states[it.first] }, { states[it.second] })
    } else {
        this.edges.groupBy({ states[it.second] }, { states[it.first] })
    }

    return from.asSequence().flatMap { ts[it]?.asSequence() ?: emptySequence() }.toSet()
}

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
