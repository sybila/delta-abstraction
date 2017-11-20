package dreal.project

import com.google.gson.*
import dreal.Rectangle
import dreal.State
import dreal.Task
import kotlinx.coroutines.experimental.newFixedThreadPoolContext
import java.io.File
import java.lang.reflect.Type

val projectRoot = "pol/"
val targetWidth = 1000.0
val pool = newFixedThreadPoolContext(Runtime.getRuntime().availableProcessors(), "abstraction")

object ModelFile : Task() {

    override val output: File = File(projectRoot, "model.bio")

    override fun run() = Unit

}

private class SerializedState(
        val tag: String,
        val r1: Rectangle?,
        val r2: Rectangle?
)

private object StateSerializer : JsonSerializer<State>, JsonDeserializer<State> {

    override fun serialize(src: State, typeOfSrc: Type, context: JsonSerializationContext): JsonElement = when (src) {
        is State.Exterior -> context.serialize(SerializedState("exterior", null, null))
        is State.Interior -> context.serialize(SerializedState("interior", src.rectangle, null))
        is State.Transition -> context.serialize(SerializedState("transition", src.from, src.to))
    }

    override fun deserialize(json: JsonElement, typeOfT: Type, context: JsonDeserializationContext): State {
        val serialized = context.deserialize<SerializedState>(json, SerializedState::class.java)
        return when (serialized.tag) {
            "exterior" -> State.Exterior
            "interior" -> State.Interior(serialized.r1!!)
            "transition" -> State.Transition(serialized.r1!!, serialized.r2!!)
            else -> error("Unknown tag ${serialized.tag}")
        }
    }

}

val json = GsonBuilder().setPrettyPrinting()
        .registerTypeAdapter(State::class.java, StateSerializer)
        .serializeSpecialFloatingPointValues()
        .create()!!