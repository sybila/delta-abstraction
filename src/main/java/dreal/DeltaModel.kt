package dreal

data class DeltaModel(
        val partitioning: Partitioning,
        val model: ModelFactory,
        val system: TransitionSystem<State>
) : ModelFactory by model