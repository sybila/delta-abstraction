package dreal

interface Solver<Param : Any> {

    /** Complete parameter set. */
    val TT: Param

    /** Intersection of the two parameter sets. */
    infix fun Param?.and(with: Param?): Param?
            = if (this == null || with == null) null else this.strictAnd(with)

    /** Union of the two parameter sets. */
    infix fun Param?.or(with: Param?): Param?
            = if (this == null) with else if (with == null) this else this.strictOr(with)

    /** Complement the target parameter set against the given set */
    infix fun Param?.complement(against: Param?): Param?
            = if (this == null || against == null) against else this.strictComplement(against)

    /**
     * Try to compute a union of the two given sets, but return it only if it contains
     * more elements, than the original target set.
     *
     * (This operation requires some kind of emptiness check)
     */
    @Suppress("IfThenToElvis")  // it will screw up the null semantics
    fun Param?.tryOr(with: Param?): Param?
            = if (with == null) null else if (this == null) with else this.strictTryOr(with)

    /**
     * An explicit emptiness check.
     * It gives you an opportunity to also simplify the formula based on the check results,
     * since you don't have to return the same parameter object. */
    fun Param.takeIfNotEmpty(): Param?

    /** @see [and] */
    fun Param.strictAnd(with: Param): Param?

    /** @see [or] */
    fun Param.strictOr(with: Param): Param?

    /** @see [complement] */
    fun Param.strictComplement(against: Param): Param?

    /** @see [tryOr] */
    fun Param.strictTryOr(with: Param): Param?

}