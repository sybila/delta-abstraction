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

fun DataOutputStream.writeState(state: State, rectangleNames: Map<Rectangle, Int>) {
    when (state) {
        is State.Exterior -> writeInt(0)
        is State.Interior -> {
            writeInt(1)
            writeInt(rectangleNames[state.rectangle]!!)
        }
        is State.Transition -> {
            writeInt(2)
            writeInt(rectangleNames[state.from]!!)
            writeInt(rectangleNames[state.to]!!)
            writeInt(rectangleNames[state.via]!!)
        }
    }
}

fun DataInputStream.readState(rectangleNames: List<Rectangle>): State {
    return when (readInt()) {
        0 -> State.Exterior
        1 -> State.Interior(rectangleNames[readInt()])
        2 -> State.Transition(rectangleNames[readInt()], rectangleNames[readInt()], rectangleNames[readInt()])
        else -> error("Unexpected state tag!")
    }
}

fun DataOutputStream.writeStates(states: List<State>) {
    val rectangleSet = HashSet<Rectangle>()
    states.forEach {
        when (it) {
            is State.Interior -> rectangleSet.add(it.rectangle)
            is State.Transition -> {
                rectangleSet.add(it.from)
                rectangleSet.add(it.to)
                rectangleSet.add(it.via)
            }
        }
    }
    val rectangleIndices = rectangleSet.toList()
    val rectangleNames = rectangleIndices.mapIndexed { i, r -> r to i  }.toMap()

    writeInt(rectangleIndices.size)
    rectangleIndices.forEach { writeRectangle(it) }
    writeInt(states.size)
    states.forEachIndexed { i, it ->
        writeState(it, rectangleNames)
    }
}

fun DataInputStream.readStates(): List<State> {
    val rectangles = Array(readInt()) { readRectangle() }.toList()
    return Array(readInt()) {
        readState(rectangles)
    }.toList()
}

fun DataOutputStream.writeTransitions(transitions: List<Pair<Int, Int>>) {
    writeInt(transitions.size)
    transitions.forEach { (a, b) ->
        writeInt(a)
        writeInt(b)
    }
}

fun DataInputStream.readTransitions(): List<Pair<Int, Int>> {
    return Array(readInt()) {
        readInt() to readInt()
    }.toList()
}