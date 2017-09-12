import java.io.File
import java.util.*


fun main(args: Array<String>) {

    val predator = "predator"
    val prey = "prey"
    val predator_0 = predator+"_0_0"
    val prey_0 = prey+"_0_0"
    val predator_1 = predator+"_0_1"
    val prey_1 = prey+"_0_1"
    val predator_t = predator+"_0_t"
    val prey_t = prey+"_0_t"
    val time_0 = "time_0"
    val time_1 = "time_1"
    val beta = str(1.33)
    val alpha = str(1.0)
    val gamma = str(1.0)
    val delta = str(1.0)
    val maxT = 1.0

    val predatorEQ = (delta mul prey mul predator) rem (gamma mul predator)
    val preyEQ = (alpha mul prey) rem (beta mul predator mul prey)

    val predatorMin = 0.5
    val predatorMax = 0.6
    val preyMin = 1.05
    val preyMax = 1.15
    /*val predatorMin = 0.1
    val predatorMax = 0.2
    val preyMin = 0.1
    val preyMax = 0.2*/


    val predatorUpperOut = conjunction(
            inInterval(predator, predatorMin, predatorMax),
            prey eq str(preyMax),
            preyEQ ge str(0.0)
    )

    val predatorUpperIn = conjunction(
            inInterval(predator, predatorMin, predatorMax),
            prey eq str(preyMax),
            preyEQ le str(0.0)
    )

    val predatorLowerIn = conjunction(
            inInterval(predator, predatorMin, predatorMax),
            prey eq str(preyMin),
            preyEQ ge str(0.0)
    )

    val predatorLowerOut = conjunction(
            inInterval(predator, predatorMin, predatorMax),
            prey eq str(preyMin),
            preyEQ le str(0.0)
    )

    val preyLowerIn = conjunction(
            predator eq str(predatorMin),
            inInterval(prey, preyMin, preyMax),
            predatorEQ ge str(0.0)
    )

    val preyLowerOut = conjunction(
            predator eq str(predatorMin),
            inInterval(prey, preyMin, preyMax),
            predatorEQ le str(0.0)
    )

    val preyUpperIn = conjunction(
            predator eq str(predatorMax),
            inInterval(prey, preyMin, preyMax),
            predatorEQ le str(0.0)
    )

    val preyUpperOut = conjunction(
            predator eq str(predatorMax),
            inInterval(prey, preyMin, preyMax),
            predatorEQ ge str(0.0)
    )


    val from = predatorLowerIn

    for (to in listOf(preyUpperOut, preyLowerOut, predatorUpperOut, predatorLowerOut)) {
        val command = ArrayList<String>().apply {
            add("(set-logic QF_NRA_ODE)")

            declareVariable(predator, 0.1, 5.0)
            declareVariable(predator_0, 0.1, 5.0)
            declareVariable(predator_1, 0.1, 5.0)
            declareVariable(predator_t, 0.1, 5.0)
            declareVariable(prey, 0.1, 5.0)
            declareVariable(prey_0, 0.1, 5.0)
            declareVariable(prey_1, 0.1, 5.0)
            declareVariable(prey_t, 0.1, 5.0)

            declareVariable(time_0, 0.0, maxT)
            declareVariable(time_1, 0.0, maxT)

            declareODE(mapOf(
                    predator to predatorEQ, prey to preyEQ
            ))

            add(assert(conjunction(
                    /*conjunction(
                            prey_0 ge str(preyMin), prey_0 le str(preyMax),
                            predator_0 ge str(predatorMin), predator_0 le str(predatorMax)
                    ),*/
                    from.replace(predator, predator_0).replace(prey, prey_0),
                    to.replace(predator, predator_t).replace(prey, prey_t),
                    // integrity constrains
                    integral0(listOf(predator_t, prey_t), listOf(predator_0, prey_0), time_0),
                    forallT(str(0.0), str(maxT), conjunction(
                            prey_t ge str(preyMin), prey_t le str(preyMax),
                            predator_t ge str(predatorMin), predator_t le str(predatorMax)
                            //predatorEQ.replace(predator, predator_t).replace(prey, prey_t)
                    ))
                    //,time_0 ge str(maxT)
                    /*integral0(listOf(predator_t, prey_t), listOf(predator_1, prey_1), time_1),
                    predator_t eq predator_1,
                    prey_t eq prey_1*/
            )))

            add("(check-sat)")
            add("(exit)")
        }

        //command.forEach { println(it) }

        val tempFile = File.createTempFile("input", ".smt2")

        tempFile.writeText(command.joinToString(separator = "\n"))

        val process = Runtime.getRuntime().exec(arrayOf("/usr/local/bin/dreal", "--visualize", tempFile.absolutePath))
        val output = process.inputStream.bufferedReader().readLines()
        println("Output: $output")
    }
}

fun MutableList<String>.declareVariable(name: String, min: Double, max: Double) {
    add("(declare-fun $name () Real [$min, $max])")
}

fun MutableList<String>.declareODE(equations: Map<String, String>) {
    add("(define-ode flow_1 ${
        equations.entries.joinToString(prefix = "(", postfix = ")", separator = " ") {
            "(= d/dt[${it.key}] ${it.value})"
        }
    })")
}

fun not(clause: String): String {
    return "(not $clause)"
}

fun conjunction(vararg clauses: String): String {
    return clauses.joinToString(separator = " ", prefix = "(and ", postfix = ")")
}

fun disjunction(vararg clauses: String): String {
    return clauses.joinToString(separator = " ", prefix = "(or ", postfix = ")")
}

fun integral0(variables: List<String>, initial: List<String>, time: String): String {
    return variables.joinToString(prefix = "[", postfix = "]", separator = " ") eq "(integral 0. $time ${initial.joinToString(prefix = "[", postfix = "]", separator = " ")} flow_1)"
}

fun forallT(time0: String, time1: String, condition: String): String {
    return "(forall_t 1 [$time0 $time1] $condition)"
}

fun inInterval(variable: String, from: Double, to: Double) = conjunction(variable ge str(from), variable le str(to))

infix fun String.ge(other: String) = "(>= $this $other)"
infix fun String.le(other: String) = "(<= $this $other)"
infix fun String.eq(other: String) = "(= $this $other)"
infix fun String.add(other: String) = "(+ $this $other)"
infix fun String.rem(other: String) = "(- $this $other)"
infix fun String.mul(other: String) = "(* $this $other)"
infix fun String.div(other: String) = "(/ $this $other)"
infix fun String.pow(other: String) = "(^ $this $other)"

fun assert(f: String) = "(assert $f)"

fun str(d: Double) = d.toString()