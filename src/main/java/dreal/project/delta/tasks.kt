package dreal.project.delta

/*
object DeltaTransitionSystemTask : Task(ApproximationTask, RectangularPartitioningTask) {

    override val output: File = File(projectRoot, "ts.delta.json")

    override fun run() {
        val ode = Parser().parse(ApproximationTask.output)
        val model = ode.toModelFactory()
        val partitioning = json.fromJson(RectangularPartitioningTask.output.readText(), Partitioning::class.java)

        val ts = model.makeStateSpace(partitioning)

        output.writeText(json.toJson(ts.system, object : TypeToken<TransitionSystem<State>>() {}.type))
    }
}*/