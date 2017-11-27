
import com.github.sybila.ode.model.Parser
import dreal.*
import java.io.File

fun main(args: Array<String>) {

    val model = Parser().parse(File("rossler/model.bio"))
    val factory = model.toModelFactory()
    val tMax = 4.0

    factory.run {
        val thresholds = listOf(0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0)
        val rectangles = thresholds.dropLast(1).zip(thresholds.drop(1)).map { (l, h) ->
            Rectangle(doubleArrayOf(l, h, -1.0, 0.0, 0.0, 0.1))
        }

        /*rectangles.forEach { r ->
            val query = """
                        ${names.makeLines { i, name -> "(declare-fun $name () Real ${r.interval(i)})" }}
                        ${names.makeLines { i, name -> "(declare-fun ${name}_0_0 () Real ${r.interval(i)})" }}
                        ${names.makeLines { i, name -> "(declare-fun ${name}_0_t () Real ${r.interval(i)})" }}

                        (declare-fun time () Real [0.0, $tMax])

                        (define-ode flow_1 (
                            ${names.makeLines { i, name -> "(= d/dt[$name] ${makeModelEquation(i)})" }}
                        ))

                        (assert (= time $tMax))
                        (assert (= [${names.joinToString(separator = " ") { it + "_0_t" }}] (integral 0. time [${names.joinToString(separator = " ") { it + "_0_0" }}] flow_1)))

                        ; WARNING: dReal is magic and these three asserts, while useless speed up the computation significantly!!
                        (assert (and ${names.makeLines { i, name ->
                "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
            }}))
                        (assert (and ${names.makeLines { i, name ->
                "(<= ${name}_0_0 ${r.bound(i, true)}) (>= ${name}_0_0 ${r.bound(i, false)})"
            }}))
                        (assert (forall_t 1 [0 time] (and ${names.makeLines { i, name ->
                "(<= ${name}_0_t ${r.bound(i, true)}) (>= ${name}_0_t ${r.bound(i, false)})"
            }})))
                    """

            //println("Check $query")
            println("Rectangle $r is ${provedUnsat(makeQuery(query))}")
        }*/
        //rectangles.forEach { bounds ->
        val zL = 2.5
        val zH = 2.8
            val bounds = Rectangle(doubleArrayOf(-1.0, 1.0, -1.0, 1.0, zL, zH))
            val sR = Rectangle(doubleArrayOf(-1.0, 1.0, -1.0, 1.0, zL, zL))//bounds.getFacet(1, false)
            val tR = Rectangle(doubleArrayOf(-1.0, 1.0, -1.0, 1.0, zH, zH))//bounds.getFacet(1, true)
            val sPositive = true
            val tPositive = true
            val sDim = 2
            val tDim = 2
            val query = """
                                ${names.makeLines { i, name -> "(declare-fun $name () Real ${bounds.interval(i)})" }}
                                ${names.makeLines { i, name -> "(declare-fun ${name}_0_0 () Real ${bounds.interval(i)})" }}
                                ${names.makeLines { i, name -> "(declare-fun ${name}_0_t () Real ${bounds.interval(i)})" }}

                                (declare-fun time () Real [0.0, $tMax])

                                (define-ode flow_1 (
                                    ${names.makeLines { i, name -> "(= d/dt[$name] ${makeModelEquation(i)})" }}
                                ))

                                (assert (= [${names.joinToString(separator = " ") { it + "_0_t" }}] (integral 0. time [${names.joinToString(separator = " ") { it + "_0_0" }}] flow_1)))

                                ; Start facet
                                (assert (and ${names.makeLines { i, name ->
                "(<= ${name}_0_0 ${sR.bound(i, true)}) (>= ${name}_0_0 ${sR.bound(i, false)})"
            }}))
                                (assert (${if (sPositive) "<" else ">" } 0 ${makeModelEquation(sDim, names = names.map { it + "_0_0" })}))

                                ; End facet
                                (assert (and ${names.makeLines { i, name ->
                "(<= ${name}_0_t ${tR.bound(i, true)}) (>= ${name}_0_t ${tR.bound(i, false)})"
            }}))
                                (assert (${if (tPositive) "<" else ">" } 0 ${makeModelEquation(tDim, names = names.map { it + "_0_t" })}))

                                (assert (forall_t 1 [0 time] (and ${names.makeLines { i, name ->
                "(<= ${name}_0_t ${bounds.bound(i, true)}) (>= ${name}_0_t ${bounds.bound(i, false)})"
            }})))
                            """

            println(query)
            println("Transition from $sR to $tR is ${provedUnsat(makeQuery(query))}")
        //}
    }
}