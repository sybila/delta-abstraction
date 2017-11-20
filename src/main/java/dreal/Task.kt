package dreal

import java.io.File

abstract class Task(val dependencies: List<Task>) {

    abstract val output: File

    constructor(vararg dependencies: Task) : this(dependencies.toList())

    fun execute() {
        for (dep in dependencies) {
            dep.execute()
        }
        val shouldReRun = dependencies.map { it.output.lastModified() }.max() ?: 0 >= output.lastModified()
        if (shouldReRun) {
            println("Executing $this")
            run()
        }
    }

    protected abstract fun run()

}