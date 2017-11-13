package dreal

data class DeltaModel(
        val partitioning: Partitioning,
        private val modelFactory: ModelFactory,
        val states: List<State>,
        val transitions: Map<State, List<State>>
) : ModelFactory by modelFactory