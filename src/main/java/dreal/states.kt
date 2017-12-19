package dreal

suspend fun ModelFactory.buildStateSpace(partitioning: Partitioning, faceSplit: Int = 0): List<State> {

    val states = ArrayList<State>()

    val unsafeInterior = partitioning.items.filter { !it.isSafe }.map { State.Interior(it.bounds) }

    val boundsRect = Rectangle(DoubleArray(dimensions * 2) { it ->
        val d = it / 2; if (it % 2 == 0) dimensionBounds(d).first else dimensionBounds(d).second
    })

    val facetStates = partitioning.items.toList().mapParallel { (rOut, _) ->
        val adjacent = ArrayList<State.Transition>()
        for ((rIn, _) in partitioning.items) {
            rOut.takeIf { it != rIn }?.getFacetIntersection(rIn)?.let { (facet, _, _) ->
                var facets = listOf(facet)
                repeat(faceSplit) {
                    facets = facets.flatMap { it.split() }
                }
                facets.forEach { face ->
                    adjacent.add(State.Transition(rOut, rIn, face))
                }
            }
        }
        boundsRect.facets.forEach { external ->
            rOut.getFacetIntersection(external)?.let { (facet, _, _) ->
                adjacent.add(State.Transition(rOut, external, facet))
                adjacent.add(State.Transition(external, rOut, facet))
            }
        }
        adjacent
    }.flatMap { it }.filterParallel { (from, to, via) ->
        val (_, d, positive) = from.getFacetIntersection(to)!!
        maybeHasFlow(via, d, positive)
    }


    states.add(State.Exterior)
    states.addAll(unsafeInterior)
    states.addAll(facetStates)

    println("Total states: ${facetStates.size}")
    return states
}

suspend fun ModelFactory.buildTransitions(partitioning: Partitioning, states: List<State>): List<Pair<Int, Int>> {

    val timeMap = partitioning.items.map { (r, t) -> r to t }.toMap()
    val indexMap = states.mapIndexed { i, state -> state to i }.toMap()

    return states.mapParallel { source ->
        source to when (source) {
            is State.Interior -> states.filter { target ->
                target == source || (target is State.Transition && source.rectangle == target.from)
            }
            is State.Exterior -> states.filter { target ->
                target == source || (target is State.Transition && target.from.degenerateDimensions > 0)
            }
            is State.Transition -> states.filter { target ->
                when (target) {
                    is State.Interior -> source.to == target.rectangle
                    is State.Exterior -> source.to.degenerateDimensions > 0
                    is State.Transition -> source.to.degenerateDimensions == 0 && source.to == target.from
                }
            }
        }
    }.flatMap { (source, successors) ->
        successors.map { source to it }
    }.filterParallel { (source, target) ->
        if (source !is State.Transition || target !is State.Transition) true else {
            val bounds = source.to
            val safetyBound = timeMap[bounds]!!
            if (safetyBound < 0.0) true else {
                val init = source.from.getFacetIntersection(source.to)!!.copy(rectangle = source.via)
                val final = target.from.getFacetIntersection(target.to)!!.copy(rectangle = target.via)

                maybeCanReach(bounds, init, final, safetyBound)
            }
        }
    }.map { (s, t) -> indexMap[s]!! to indexMap[t]!! }

}