package fortress.util

trait Time {
    def asMilliLong: Long
    def asNanoLong: Long
    def prettyPrint: String
}
