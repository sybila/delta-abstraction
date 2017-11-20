package dreal

import dreal.project.Partitioning
import dreal.project.TransitionSystem

data class DeltaModel(
        val partitioning: Partitioning,
        val model: ModelFactory,
        val system: TransitionSystem<State>
) : ModelFactory by model