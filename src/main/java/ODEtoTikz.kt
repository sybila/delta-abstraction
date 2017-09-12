
import java.io.File
import java.util.*

fun main(args: Array<String>) {

    File("picture.tex").outputStream().bufferedWriter().use { picture ->
        picture.write("""
            \documentclass[border=10pt]{standalone}

            \usepackage{tikz}
            \usepackage{amsfonts}
            \usepackage{amssymb}
            \usepackage{amsmath}
            \usetikzlibrary{arrows.meta}
            \usetikzlibrary{arrows,shapes,automata,backgrounds,petri}
            \usetikzlibrary{positioning}

            \tikzset{up/.style={draw, shape=circle, fill=red}}
            \tikzset{down/.style={draw, shape=circle, fill=blue}}
            \tikzset{loop/.style={-{latex[length=3mm]}}}

            \begin{document}
            \begin{tikzpicture}[]
        """)

        //val thresholdsX = listOf(0.5, 0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.3, 1.4, 1.5)
        //val thresholdsY = listOf(0.5, 0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.3, 1.4, 1.5)
        val thresholdsX = listOf(-5.0,-4.0,-3.0,-2.0,-1.0,0.0,1.0,2.0,3.0,4.0,5.0)
        val thresholdsY = listOf(-5.0,-4.0,-3.0,-2.0,-1.0,0.0,1.0,2.0,3.0,4.0,5.0)
        val minX = thresholdsX.first() - 0.1
        val maxX = thresholdsX.last() + 0.1
        val minY = thresholdsY.first() - 0.1
        val maxY = thresholdsY.last() + 0.1

        val boxesX = thresholdsX.size - 1
        val boxesY = thresholdsY.size - 1

        for (x in 0 until boxesX) {
            for (y in 0 until boxesY) {
                //X dimension - x is free, y is fixed
                picture.write("\\node[down] (${encode(x, y, true, false)}) at (${2*x + 0.6}, ${2*y}) {}; \n")
                picture.write("\\node[up] (${encode(x, y, true, true)}) at (${2*x + 1.4}, ${2*y}) {}; \n")

                //Y dimension - y is free, x is fixed
                picture.write("\\node[down] (${encode(x, y, false, false)}) at (${2*x}, ${2*y + 0.6}) {}; \n")
                picture.write("\\node[up] (${encode(x, y, false, true)}) at (${2*x}, ${2*y + 1.4}) {}; \n")
            }
        }

        for (x in 0 until boxesX) {
            //X dimension - x is free, y is fixed
            val y = boxesY
            picture.write("\\node[down] (${encode(x, y, true, false)}) at (${2*x + 0.6}, ${2*y}) {}; \n")
            picture.write("\\node[up] (${encode(x, y, true, true)}) at (${2*x + 1.4}, ${2*y}) {}; \n")
        }

        for (y in 0 until boxesY) {
            //horizontal
            val x = boxesX
            picture.write("\\node[down] (${encode(x, y, false, false)}) at (${2*x}, ${2*y + 0.6}) {}; \n")
            picture.write("\\node[up] (${encode(x, y, false, true)}) at (${2*x}, ${2*y + 1.4}) {}; \n")
        }

        //picture.write("\\draw[loop] (${encode(0,0, true, true)}) -- (${encode(1,0, false, true)});")

        val transitions = ArrayList<Pair<String, String>>()

        for (x in 0 until boxesX) {
            for (y in 0 until boxesY) {
                val Xlow = thresholdsX[x]
                val Xhigh = thresholdsX[x+1]
                val Ylow = thresholdsY[y]
                val Yhigh = thresholdsY[y+1]

                val X = "x"
                val Y = "y"
                val X_0 = X+"_0_0"
                val X_t = X+"_0_t"
                val Y_0 = Y+"_0_0"
                val Y_t = Y+"_0_t"
                val time_0 = "time_0"
                val maxT = 2.0
                //val equationX = Y rem X
                //val equationY = ("(- $X)" rem Y) add str(2.0)
                //val equationX = X rem (str(1.33) mul X mul Y)
                //val equationY = (X mul Y) rem Y
                val equationX = (X rem (X mul X mul X mul str(0.33))) rem Y
                val equationY = X


                val horizontalLower = Facet(X, Y, Xlow to Xhigh, Ylow, equationY, false, x to y)
                val horizontalUpper = Facet(X, Y, Xlow to Xhigh, Yhigh, equationY, true, x to (y+1))
                val verticalLower = Facet(Y, X, Ylow to Yhigh, Xlow, equationX, false, x to y)
                val verticalUpper = Facet(Y, X, Ylow to Yhigh, Xhigh, equationX, true, (x+1) to y)

                val facets = listOf(horizontalLower, horizontalUpper, verticalLower, verticalUpper)

                for (incoming in facets) {
                    for (outgoing in facets) {

                        val incomingPositive = !incoming.upper
                        val outgoingPositive = outgoing.upper

                        val incomingProposition = conjunction(
                            incoming.fixedDimension eq str(incoming.fixed),
                                range(incoming.rangeDimension, incoming.range.first, incoming.range.second),
                                if (incomingPositive) incoming.equation ge str(0.0)
                                else incoming.equation le str(0.0)
                        )

                        val outgoingProposition = conjunction(
                                outgoing.fixedDimension eq str(outgoing.fixed),
                                range(outgoing.rangeDimension, outgoing.range.first, outgoing.range.second),
                                if (outgoingPositive) outgoing.equation ge str(0.0)
                                else outgoing.equation le str(0.0)
                        )

                        val command = ArrayList<String>().apply {
                            add("(set-logic QF_NRA_ODE)")
                            declareVariable(X, minX, maxX)
                            declareVariable(X_0, minX, maxX)
                            declareVariable(X_t, minX, maxX)
                            declareVariable(Y, minY, maxY)
                            declareVariable(Y_0, minY, maxY)
                            declareVariable(Y_t, minY, maxY)
                            declareVariable(time_0, 0.0, maxT)

                            declareODE(mapOf(X to equationX, Y to equationY))

                            // check reach
                            add(assert(conjunction(
                                    incomingProposition.replace(X, X_0).replace(Y, Y_0),
                                    outgoingProposition.replace(X, X_t).replace(Y, Y_t),
                                    integral0(listOf(X_t, Y_t), listOf(X_0, Y_0), time_0),
                                    forallT(str(0.0), str(maxT), conjunction(
                                            X_t ge str(Xlow), X_t le str(Xhigh),
                                            Y_t ge str(Ylow), Y_t le str(Yhigh),
                                            not(equationX.replace(X, X_t).replace(Y, Y_t) eq str(0.0)),
                                            not(equationY.replace(X, X_t).replace(Y, Y_t) eq str(0.0))
                                    ))
                            )))


                            //check time validity
                            /*add(assert(conjunction(
                                    // we are in the box
                                    X_0 ge str(Xlow), X_0 le str(Xhigh),
                                    Y_0 ge str(Ylow), Y_0 le str(Yhigh),
                                    // X/Y_t is a curve position at time t_0
                                    integral0(listOf(X_t, Y_t), listOf(X_0, Y_0), time_0),
                                    // the whole curve is inside the box
                                    forallT(str(0.0), str(maxT), conjunction(
                                            X_t ge str(Xlow), X_t le str(Xhigh),
                                            Y_t ge str(Ylow), Y_t le str(Yhigh),
                                            not(equationX.replace(X, X_t).replace(Y, Y_t) eq str(0.0)),
                                            not(equationY.replace(X, X_t).replace(Y, Y_t) eq str(0.0))
                                    )),
                                    // and the whole curve actually uses all the time available
                                    time_0 ge str(maxT)
                            )))*/

                            add("(check-sat)")
                            add("(exit)")
                        }

                        val tempFile = File.createTempFile("input", ".smt2")

                        //for (c in command) println(c)

                        tempFile.writeText(command.joinToString(separator = "\n"))

                        val process = Runtime.getRuntime().exec(arrayOf("/usr/local/bin/dreal", /*"--visualize",*/ tempFile.absolutePath))
                        val output = process.inputStream.bufferedReader().readLines()
                        println("Output($x, $y): $output")

                        if (output != listOf("unsat")) {
                            val from = encode(incoming.coordinates.first, incoming.coordinates.second, incoming.rangeDimension == X, incomingPositive)
                            val to = encode(outgoing.coordinates.first, outgoing.coordinates.second, outgoing.rangeDimension == X, outgoingPositive)
                            picture.write("\\draw[loop] ($from) -- ($to); \n")
                            transitions.add(from to to)
                        }

                    }
                }
            }

            val T = transitions.groupBy({ it.first }, { it.second })

            var states = listOf(encode(boxesX / 2,boxesY / 2, false, true))
            //var states = listOf(encode(0,boxesY, true, false))
            var newStates = states

            do {
                states = newStates
                newStates = (states + (states.flatMap { T[it] ?: listOf() })).toSet().toList()
            } while (states != newStates)

            for (state in states) {
                picture.write("\\node[fill=green, below right= 0.01cm and 0.01cm of $state] (copy$state) {};")
                //picture.write("\\draw[loop] ($state) -- ($state); \n")
            }
        }

        picture.write("""
            \end{tikzpicture}
            \end{document}
        """)

    }

    /*println("Picture written")

    Runtime.getRuntime().exec(arrayOf("pdflatex", "picture")).waitFor()

    println("pdf done... openning...")

    Runtime.getRuntime().exec(arrayOf("open", "picture.pdf")).waitFor()*/
}

data class Facet(
        val rangeDimension: String,
        val fixedDimension: String,
        val range: Pair<Double, Double>,
        val fixed: Double,
        val equation: String,
        val upper: Boolean,
        val coordinates: Pair<Int, Int>
)

private fun range(v: String, from: Double, to: Double): String
        = conjunction(v ge str(from), v le str(to))

private fun encode(x: Int, y: Int, Xdim: Boolean, up: Boolean)
        = "${if (up) "p" else "n"}-$x-$y-${if (Xdim) "x" else "y"}"