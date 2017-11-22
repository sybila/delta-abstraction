
import dreal.project.Delta
import dreal.project.PWMA
import dreal.project.TaskGraph

fun main(args: Array<String>) {

    PWMA.Approximation
    PWMA.Partition
    PWMA.Partition.Svg
    //PWMA.Transitions
    //PWMA.Transitions.Svg
    //PWMA.TerminalComponents
    //PWMA.TerminalComponents.Svg
    Delta.Rectangular.All
    Delta.Rectangular.All.Svg
    Delta.Rectangular.States
    Delta.Rectangular.States.Svg
    Delta.Rectangular.Transitions
    Delta.Rectangular.Transitions.Svg
    Delta.Rectangular.TerminalComponents
    Delta.Rectangular.TerminalComponents.Svg
    Delta.Rectangular.InitialComponents
    Delta.Rectangular.InitialComponents.Svg
    //Delta.Rectangular.Cycles
    //Delta.Rectangular.Cycles.Svg

    //Delta.Rectangular.Transitions.output.delete()

    TaskGraph.make()
}