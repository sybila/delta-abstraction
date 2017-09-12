package dreal

import kotlinx.coroutines.experimental.runBlocking

fun main(args: Array<String>) {
    runBlocking {
        G1Sswitch.makePartitions()
    }
}