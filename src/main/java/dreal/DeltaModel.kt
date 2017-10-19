package dreal

data class DeltaModel(
        val states: List<State>,
        val transitions: Map<State, List<State>>
)