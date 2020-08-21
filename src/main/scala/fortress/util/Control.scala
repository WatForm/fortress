package fortress.util

object Control {
    def measureTime[A](block: => A): (A, Nanoseconds) = {
        val stopwatch = new StopWatch
        stopwatch.startFresh()

        val result = block

        val elapsed = stopwatch.elapsedNano
        (result, elapsed)
    }

    def withStopWatch[A](block: StopWatch => A): A = {
        val stopwatch = new StopWatch
        stopwatch.startFresh()

        block(stopwatch)
    }

    def withCountdown[A](maxTime: Milliseconds)(block: CountdownTimer => A): A = {
        block(new CountdownTimer(maxTime))
    }
}