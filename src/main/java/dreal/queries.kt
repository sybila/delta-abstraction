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
"""

    return provedUnsat(makeQuery(query))
}

fun ModelFactory.maybeHasFlow(r: Rectangle, d: Int, positive: Boolean): Boolean {

    val query =
"""
; Declare model variables
${names.makeLines { i, name -> "(declare-fun $name () Real ${r.interval(i)})" }}

; Declare equation is positive/negative
(assert (${if (positive) "<" else ">" } 0 ${makeModelEquation(d)}))
"""

    return !provedUnsat(makeQuery(query))

}