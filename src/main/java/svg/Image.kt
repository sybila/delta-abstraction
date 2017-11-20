package svg

/**
 * Image is a common supertype for all objects which can be converted into an [SvgImage].
 */
interface Image {

    fun toSvgImage(): SvgImage

}