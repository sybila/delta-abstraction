
import dreal.project.Delta
import dreal.project.TaskGraph
import dreal.project.makeExperiments

fun main(args: Array<String>) {

    //PWMA.Approximation
    //PWMA.Partition
    //Delta.Tile.Herringbone
    //Delta.Tile.Herringbone.Svg
    //Delta.Tile.Diagonal
    //Delta.Tile.Diagonal.Svg
    /*//PWMA.Herringbone.Svg
    //PWMA.Transitions
    //PWMA.Transitions.Svg
    //PWMA.TerminalComponents
    //PWMA.TerminalComponents.Svg
    Delta.Rectangular.All
    Delta.Rectangular.All.Svg
    Delta.Rectangular.States
    //Delta.Rectangular.States.Svg
    Delta.Rectangular.Transitions
    //Delta.Rectangular.Transitions.Svg
    Delta.Rectangular.TerminalComponents
    Delta.Rectangular.TerminalComponents.Svg
    Delta.Rectangular.InitialComponents
    //Delta.Rectangular.InitialComponents.Svg
    //Delta.Rectangular.Cycles
    //Delta.Rectangular.Cycles.Svg

    //Delta.Rectangular.Transitions.output.delete()

    //Delta.Rectangular.BlenderExportTerminal*/

    Delta.Tile.BigSmall.Svg
    makeExperiments(Delta.Tile.BigSmall)
/*
    val Transitions = object : JsonTask<TransitionSystem<State>>("ts.transitions.delta.json", type<TransitionSystem<State>>()) {}
    val TerminalComponents = object : JsonTask<List<State>>("prop.delta.json", type<List<State>>(), Transitions) {
        override fun run() {
            val ts = Transitions.readJson()
            val partition = Delta.Tile.BigSmall.readJson()
            val rect = partition.items[535].bounds
            val initial = ts.states.filter { when (it) {
                is State.Exterior -> false
                is State.Interior -> it.rectangle == rect
                is State.Transition -> it.from == rect || it.to == rect
            } }.toSet()
            var prop = initial
            repeat(4) {
                prop = ts.next(prop)
            }
            writeJson(prop.toList())
        }

        val Svg = DeltaTransitionSystemPropertySvgTask("prop.delta.svg",
                Delta.Tile.BigSmall, Transitions, this
        )
    }

    TerminalComponents.output.delete()*/
    TaskGraph.make()
}