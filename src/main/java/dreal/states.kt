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