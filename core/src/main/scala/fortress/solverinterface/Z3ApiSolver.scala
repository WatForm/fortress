package fortress.solverinterface

import fortress.util.Milliseconds

class Z3ApiSolver extends Z3PythonProcessBuilderSolver {
    // Call the python executable
    protected def processArgs: Seq[String] = Seq("python3", "test_print.py")
    // Currently no timeout implementation
    protected def timeoutArg(timeoutMillis: Milliseconds): String = ""
}
