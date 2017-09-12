package dreal

object G1Sswitch : ModelFactory {

    override val names: List<String> = listOf("x", "y", "p")

    private fun HillP(x: String, t: String) = "(/ ($x) (+ ($x) ($t)))"

    private fun HillN(x: String, t: String) = "(/ ($t) (+ ($x) ($t)))"


    override fun makeModelEquation(i: Int, names: List<String>): String = when (i) {
        0 -> "(- (* ${HillP(y, "0.5")} ${HillN(x, "0.5")}) (* $p $x))"
        1 -> {
            val xN = HillN(x, "5")
            "(- (+ (0.05) (* (0.00016) ${HillN("(* $y $y)", "16")} $xN) (* (1.6) ${HillP("(* $y $y)", "16")} $xN)) (* 0.1 $y))"
        }
        2 -> "0"
        else -> unknownDimension(i)
    }

    override fun dimensionBounds(i: Int): Pair<Double, Double> = when (i) {
        0 -> 0.0 to 10.0
        1 -> 0.0 to 10.0
        2 -> 0.001 to 0.1
        else -> unknownDimension(i)
    }

}