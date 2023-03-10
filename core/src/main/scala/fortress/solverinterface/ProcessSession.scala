package fortress.solverinterface

import java.io._
import java.lang.AutoCloseable

// Cannot be cleared -- make a new session
class ProcessSession(processArgs: java.util.List[String]) extends AutoCloseable {
    private val process: Process = new ProcessBuilder(processArgs).start()
    private val in: BufferedWriter = new BufferedWriter(new OutputStreamWriter(process.getOutputStream))
    private val out: BufferedReader = new BufferedReader(new InputStreamReader(process.getInputStream))
    
    def flush(): Unit = in.flush()
    def write(str: String): Unit = in.write(str)
    def readLine(): String = out.readLine()
    def inputWriter: Writer = in

    def isAlive: Boolean = process.isAlive

    override protected def finalize(): Unit = close()
    
    @throws(classOf[java.io.IOException])
    override def close(): Unit = {
        in.close()
        out.close()
        process.waitFor()
        process.destroy()
    }
    
}
