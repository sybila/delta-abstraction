package dreal.project

/*
object DeltaTransitionSystemSvg : Task(DeltaTransitionSystemTask, RectangularPartitioningTask) {
    override val output: File = File(projectRoot, "ts.delta.svg")

    override fun run() {
        val partitioning = json.fromJson(RectangularPartitioningTask.output.readText(), Partitioning::class.java)
        val type = object : TypeToken<TransitionSystem<State>>() {}.type
        val system = json.fromJson<TransitionSystem<State>>(DeltaTransitionSystemTask.output.readText(), type)

        output.writeText(DeltaImage(partitioning, system, emptySet()).toSvgImage().normalize(targetWidth).compileSvg())
    }
}*/