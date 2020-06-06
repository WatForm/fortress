package fortress.util

import java.lang.IllegalStateException

class StopWatch {
    
    var start: Nanoseconds = Nanoseconds(-1L)
    var running: Boolean = false
    
    def startFresh(): Unit = {
        start = Nanoseconds(System.nanoTime())
        running = true
    }
    
    // Returns the elapsed time in nanoseconds
    def elapsedNano(): Nanoseconds = {
        if(!running) {
            throw new IllegalStateException()
        }
        val now: Nanoseconds = Nanoseconds(System.nanoTime())
        now - start
    }
    
}
