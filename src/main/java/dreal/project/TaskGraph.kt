package dreal.project

object TaskGraph {

    /**
     * This stores the task graph sorted using the task dependencies.
     *
     * We assume that the number of tasks will not be very high (up to 1000), so we don't
     * implement any intelligent lookup for this.
     *
     * Go level after level and check if any dependency modification date is newer than the current output.
     * If it is, recompute the task. By following the levels, you ensure proper dependency order.
     */
    private val tasks = ArrayList<MutableSet<Task>>()

    fun register(task: Task) {
        if (tasks.any { task in it }) error("$task already registered.")
        task.dependencies.forEach { registerWithStack(it, emptyList()) }
        insert(task)
    }

    /**
     * A private register function which also checks that all dependencies are recursively registered
     * and that there are no cyclic dependencies.
     */
    private fun registerWithStack(task: Task, pending: List<Task>) {
        if (task in pending) error("Cyclic dependency in chain: $pending.")
        if (tasks.all { task !in it }) {
            // Only register if not already present, otherwise do nothing.
            task.dependencies.forEach { registerWithStack(it, pending + task) }
            insert(task)
        }
    }

    /**
     * Call this only once you know all dependencies are registered and the given [task] is not.
     */
    private fun insert(task: Task) {
        val insertIndex: Int = (task.dependencies.map { d -> tasks.indexOfFirst { d in it } }.max() ?: -1) + 1
        while (tasks.size <= insertIndex) tasks.add(mutableSetOf())
        tasks[insertIndex].add(task)
    }

    /**
     * Execute all tasks in the correct order.
     */
    fun make() {
        tasks.forEach { level ->
            level.forEach { task ->
                val lastChange = task.dependencies.map { it.output.lastModified() }.max() ?: 0
                val shouldRun = !task.output.exists() || task.output.lastModified() <= lastChange
                if (shouldRun) {
                    println("Executing $task")
                    task.run()
                }
            }
        }
    }

    fun clean() {
        // skip 0 level
        tasks.drop(1).forEach { level ->
            level.forEach { task ->
                println("Clean $task")
                task.output.delete()
            }
        }
    }

}