package dreal

import java.util.*

class Grid1Solver(
        boundsX: Pair<Double, Double>
) : Solver<Grid1> {

    override val TT: Grid1 = Grid1(
            thresholds = doubleArrayOf(boundsX.first, boundsX.second),
            values = BitSet(1).apply { set(0) }
    )

    override fun Grid1.takeIfNotEmpty(): Grid1? = if (this != Grid1.EMPTY) this else null

    override fun Grid1.strictAnd(with: Grid1): Grid1? {
        val (l, r) = this.cut(with) to with.cut(this)
        return l.copy(values = l.values.copy().apply { and(r.values) }).simplify().takeIfNotEmpty()
    }

    override fun Grid1.strictOr(with: Grid1): Grid1? {
        val (l, r) = this.cut(with) to with.cut(this)
        return l.copy(values = l.values.copy().apply { or(r.values) }).simplify().takeIfNotEmpty()
    }

    override fun Grid1.strictComplement(against: Grid1): Grid1? {
        val (l, r) = this.cut(against) to against.cut(this)
        return r.copy(values = r.values.copy().apply { andNot(l.values) }).simplify()
    }

    override fun Grid1.strictTryOr(with: Grid1): Grid1? {
        return this.strictOr(with)?.let {
            if (it != this) it else null
        }
    }

    private fun BitSet.copy() = this.clone() as BitSet

}