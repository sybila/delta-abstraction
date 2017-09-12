import java.io.File

interface Formula {
    fun eval(): Boolean
}

data class Atom(private val value: Boolean): Formula {
    override fun eval(): Boolean = value
}

data class Placeholder(val index: Int): Formula {
    override fun eval(): Boolean {
        throw UnsupportedOperationException()
    }

    override fun toString(): String {
        return ('A'..'Z').toList()[index].toString()
    }
}

data class Impl(val X: Formula, val Y: Formula): Formula {
    override fun eval(): Boolean = !X.eval() || Y.eval()
    override fun toString(): String {
        return "($X -> $Y)"
    }
}

infix fun Formula.implies(other: Formula) = Impl(this, other)
fun Formula.replacePlaceholders(vals: List<Boolean>): Formula {
    if (this is Placeholder) return Atom(vals[index])
    else if (this is Impl) return (X.replacePlaceholders(vals)) implies (Y.replacePlaceholders(vals))
    else return this
}

fun Char.v(): Placeholder = Placeholder(this.toInt() - 'A'.toInt())
/*
fun main(args: Array<String>) {
    val valuations = setOf(true, false).crypto.pow(10)//.map { list -> list.map { Atom(it) } }
    var count = 0
    val A = 'A'.v()
    val B = 'B'.v()
    val C = 'C'.v()
    val D = 'D'.v()
    val E = 'E'.v()
    val F = 'F'.v()
    val G = 'G'.v()
    /*val form = (
            (
                    A implies (B implies (C implies D)) implies G
            )
                implies
            (
                    ((D implies E) implies F)
            )
        )*/
    //val form = ((((A implies (B implies C)) implies D) implies (C implies G)) implies (F))
    val form = (((((A implies B) implies C) implies D) implies (E implies F)) implies G)
    //72: val form = ((((A implies (B implies C)) implies D) implies (C implies B)) implies (F))
    for (vals in valuations) {
        val f = form.replacePlaceholders(vals)
        if (f.eval()) count++
    }
    println("C: $count")
    /*val formulas = HashSet<Formula>()
    formulas.addAll((0..6).map { Placeholder(it) })
    while (formulas.size() < 50000) {
        println(formulas.size())
        val newFormulas = HashSet<Formula>()
        for (f1 in formulas) {
            for (f2 in formulas) {
                val f3 = f1 implies f2
                var count = 0
                for (vals in valuations) {
                    val f = f3.replacePlaceholders(vals)
                    if (f.eval()) count++
                }
                if (count == 75) {
                    println("Got formula! $f3")
                }
                newFormulas.add(f3)
            }
        }
        formulas.addAll(newFormulas)
    }*/
   // inspect(10, 600)
}*/
/*
fun inspect(n: Int, target: Int) {
    if (n == 1) {
        println("Success")
        return
    }
    val ijs = ((1..(n-1)).toSet() times (1..(n-1)).toSet()).filter { it.first + it.second == n }
    for ((i, j) in ijs) {
        for (x in (pow(2, i-1)..pow(2, i))) {
            val res = target - pow(2, j) * (pow(2, i) - x)
            if (res % x == 0 && res/x > pow(2, j-1)) {
                println("Got $i, $j, $x, ${res/x}")
                inspect(j, res/x)
            }
        }
    }
}*/

fun pow(i: Int, j: Int):Int {
    return Math.pow(i.toDouble(), j.toDouble()).toInt()
}

fun main(args: Array<String>) {
    //val root = File("/Users/daemontus/Downloads/facebook.arm.5")
    val root = File("/Users/daemontus/Downloads/messenger")

    val count = root.listFiles()
            .filter { it.name.startsWith("classes") && it.isDirectory }
            .fold(0) { acc, it ->
                // explore class directory
                val Xdir = File(it, "X")
                val comDotFacebookDir = File(File(it, "com"), "facebook")
                acc + Xdir.countClasses() + comDotFacebookDir.countClasses()
            }

    println("Count $count")

    //println("Classes: ${root.countClasses()}")

}

fun File.countClasses(): Int {
    return if (this.isDirectory) {
        val r = this.listFiles().fold(0) { acc, f -> acc + f.countClasses() }
        println(this.path + " " + r)
        r
    } else {
        if (this.name.endsWith(".class") || this.name.endsWith(".smali")) 1 else 0
    }
}