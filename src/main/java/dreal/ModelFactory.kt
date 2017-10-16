package dreal

/**
 * A model with two dimensions and one parameter
 */
interface ModelFactory {

    val names: List<String>

    val variables: List<String>
        get() = names.dropLast(1)

    val x: String
        get() = names[0]

    val y: String
        get() = names[1]

    val p: String
        get() = names[2]

    fun makeModelEquation(i: Int, names: List<String> = this.names): String

    fun dimensionBounds(i: Int): Pair<Double, Double>

    fun makeHead(suffix: String = ""): String =
"""
(declare-fun $x$suffix () Real [${dimensionBounds(0).let { (l, h) -> "$l, $h" }}])
(declare-fun $y$suffix () Real [${dimensionBounds(1).let { (l, h) -> "$l, $h" }}])
(declare-fun $p$suffix () Real [${dimensionBounds(2).let { (l, h) -> "$l, $h" }}])
""".trim()

    fun makeEqulibrium(): String =
"""
(assert (= 0 ${makeModelEquation(0)}))
(assert (= 0 ${makeModelEquation(1)}))
""".trim()

    fun makeFixedEqulibrium(p: Double): String =
            """
(assert (= 0 ${makeModelEquation(0, variables + p.toString())}))
(assert (= 0 ${makeModelEquation(1, variables + p.toString())}))
""".trim()


    fun makeFlow(): String =
"""
(define-ode flow_1 ((= d/dt[$x] ${makeModelEquation(0)}) (= d/dt[$y] ${makeModelEquation(1)}) (= d/dt[$p] 0)))
""".trim()

    fun makeFixedFlow(p: Double): String =
"""
(define-ode flow_1 ((= d/dt[$x] ${makeModelEquation(0, variables + p.toString())}) (= d/dt[$y] ${makeModelEquation(1, variables + p.toString())})))
""".trim()

    fun unknownDimension(i: Int): Nothing = error("Dimension  $i does not exist in $this")

}