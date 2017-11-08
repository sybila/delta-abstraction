package dreal

data class DeltaModel(
        val partitioning: List<Rectangle>,
        private val modelFactory: ModelFactory,
        val states: List<State>,
        val transitions: Map<State, List<State>>
) : ModelFactory by modelFactory