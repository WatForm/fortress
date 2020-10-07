package fortress.util

object Errors2 {
    def tryDebug[A](block: => A)(ifFail: => Unit): A = {
        try {
            block
        } catch {
            case e: Exception => {
                ifFail
                throw e
            }
        }
    }
}