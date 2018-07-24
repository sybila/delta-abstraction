package dreal

inline fun List<String>.makeLines(action: (Int, String) -> String): String = this.mapIndexed(action).joinToString(separator = "\n")

fun Rectangle.interval(dim: Int): String = "[${lBound(dim)}, ${hBound(dim)}]"

fun ModelFactory.maybeHasZero(r: Rectangle): Boolean {

    val query =
"""
; Declare model variables.
${names.makeLines { i, name -> "(declare-fun $name () Real ${r.interval(i)})" }}

; Assert that each equation is equal to zero.
${names.makeLines { i, _ -> "(assert (= 0 ${makeModelEquation(i, names)}))" }}
"""

    return !provedUnsat(makeQuery(query))
}

fun ModelFactory.isSafeWithin(r: Rectangle, t: Double): Boolean {

    val query =
"""
; Declare model variables, initial curve points and final curve points.
${names.makeLines { i, name -> "(declare-fun $name () Real ${r.interval(i)})" }}
${names.makeLines { i, name -> "(declare-fun ${name}_0_0 () Real ${r.interval(i)})" }}
${names.makeLines { i, name -> "(declare-fun ${name}_0_t () Real ${r.interval(i)})" }}

; Declare time variable.
(declare-fun time () Real [0.0, $t])

; Declare flow equations.
(define-ode flow_1 (
    ${names.makeLines { i, name -> "(= d/dt[$name] ${makeModelEquation(i)})" }}
))

; Declare curve of length $t
(assert (= time $t))
(assert (= [${names.joinToString(separator = " ") { it + "_0_t" }}]
    (integral 0. time [${names.joinToString(separator = " ") { it + "_0_0" }}] flow_1)
))

; dReal is magic and these three asserts, while useless speed up the computation significantly!!
(assert (and ${names.makeLines { i, name ->
"(>= ${name}_0_t ${r.lBound(i)}) (<= ${name}_0_t ${r.hBound(i)})"
}}))
(assert (and ${names.makeLines { i, name ->
"(>= ${name}_0_0 ${r.lBound(i)}) (<= ${name}_0_0 ${r.hBound(i)})"
}}))
(assert (forall_t 1 [0 time] (and ${names.makeLines { i, name ->
"(>= ${name}_0_t ${r.lBound(i)}) (<= ${name}_0_t ${r.hBound(i)})"
}})))
"""//.also { println(it); error("stop") }

    return provedUnsat(makeQuery(query))
}

fun ModelFactory.maybeHasFlow(r: Rectangle, d: Int, positive: Boolean): Boolean {

    val hasFlowInVertex = r.vertices.any { vertex ->
        val value = evalModelEquation(d, vertex)
        (positive && value > 0) || (!positive && value < 0)
    }

    if (hasFlowInVertex) return true

    val query =
"""
; Declare model variables
${names.makeLines { i, name -> "(declare-fun $name () Real ${r.interval(i)})" }}

; Declare equation is positive/negative
(assert (${if (positive) "<" else ">" } 0 ${makeModelEquation(d)}))
"""//.also { if (d == 0 && !positive) println(it) }

    return !provedUnsat(makeQuery(query))

}

fun ModelFactory.maybeCanReach(bounds: Rectangle, from: Rectangle.FacetIntersection, to: Rectangle.FacetIntersection, t: Double): Boolean {

    val (sR, sDim, sPositive) = from
    val (tR, tDim, tPositive) = to

    /*val common = sR.getIntersection(tR)
    if (common != null) {
        val hasSinglePointFlow = common.vertices.any { vertex ->
            val source = evalModelEquation(sDim, vertex)
            val target = evalModelEquation(tDim, vertex)
                    ((sPositive && source > 0) || (!sPositive && source < 0)) &&
                    ((tPositive && target > 0) || (!tPositive && target < 0))
        }
        if (hasSinglePointFlow) return true
    }*/

    val query =
"""
; Declare model variables, initial curve points and final curve points.
${names.makeLines { i, name -> "(declare-fun $name () Real ${bounds.interval(i)})" }}
${names.makeLines { i, name -> "(declare-fun ${name}_0_0 () Real ${bounds.interval(i)})" }}
${names.makeLines { i, name -> "(declare-fun ${name}_0_t () Real ${bounds.interval(i)})" }}

; Declare time variable.
(declare-fun time () Real [0.0, $t])

; Declare flow equations.
(define-ode flow_1 (
    ${names.makeLines { i, name -> "(= d/dt[$name] ${makeModelEquation(i)})" }}
))

; Declare curve of length <= $t
(assert (= [${names.joinToString(separator = " ") { it + "_0_t" }}]
    (integral 0. time [${names.joinToString(separator = " ") { it + "_0_0" }}] flow_1)
))

; Start facet
(assert (and ${names.makeLines { i, name ->
    "(<= ${name}_0_0 ${sR.hBound(i)}) (>= ${name}_0_0 ${sR.lBound(i)})"
}}))
(assert (${if (sPositive) "<" else ">" } 0 ${makeModelEquation(sDim, names = names.map { it + "_0_0" })}))

; End facet
(assert (and ${names.makeLines { i, name ->
    "(<= ${name}_0_t ${tR.hBound(i)}) (>= ${name}_0_t ${tR.lBound(i)})"
}}))
(assert (${if (tPositive) "<" else ">" } 0 ${makeModelEquation(tDim, names = names.map { it + "_0_t" })}))

(assert (forall_t 1 [0 time] (and ${names.makeLines { i, name ->
    "(<= ${name}_0_t ${bounds.hBound(i)}) (>= ${name}_0_t ${bounds.lBound(i)})"
}})))
"""

    return !provedUnsat(makeQuery(query))
}