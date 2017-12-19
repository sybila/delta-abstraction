package dreal

import java.io.DataInputStream
import java.io.DataOutputStream

fun DataOutputStream.writeRectangle(rectangle: Rectangle) {
    writeInt(rectangle.array.size)
    rectangle.array.forEach { writeDouble(it) }
}

fun DataInputStream.readRectangle(): Rectangle
        = Rectangle(DoubleArray(readInt()) { readDouble() })

fun DataOutputStream.writePartitioning(partitioning: Partitioning) {
    writeInt(partitioning.items.size)
    partitioning.items.forEach {
        writeRectangle(it.bounds)
        writeDouble(it.provedSafe)
    }
}

fun DataInputStream.readPartitioning(): Partitioning {
    val size = readInt()
    val list = ArrayList<Partitioning.Item>(size)
    repeat(size) {
        val bounds = readRectangle()
        val provedSafe = readDouble()
        list.add(Partitioning.Item(bounds, provedSafe))
    }
    return Partitioning(list.toSet())
}