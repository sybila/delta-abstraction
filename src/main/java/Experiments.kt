
import dreal.project.Delta
import dreal.project.PWMA
import dreal.project.TaskGraph
import dreal.project.makeExperiments

fun main(args: Array<String>) {

    PWMA.Approximation
    //PWMA.Partition
    //Delta.Tile.Herringbone
    //Delta.Tile.Herringbone.Svg
    Delta.Tile.Diagonal
    Delta.Tile.Diagonal.Svg
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

    makeExperiments(Delta.Tile.Diagonal)

    TaskGraph.make()
}