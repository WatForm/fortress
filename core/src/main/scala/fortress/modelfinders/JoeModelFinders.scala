package fortress.modelfinders

import fortress.solvers._
import fortress.compilers._

abstract class JoeModelFinder extends ModelFinder {
    setSolver(new Z3NonIncCliSolver()) 
}

class JoeZEROModelFinder extends JoeModelFinder {
    setCompiler(new JoeZEROCompiler())
}

class JoeONEModelFinder extends JoeModelFinder {
    setCompiler(new JoeONECompiler())
}

class JoeTWOModelFinder  extends JoeModelFinder {
    setCompiler(new JoeTWOCompiler())
}

class JoeTWO_SIModelFinder  extends JoeModelFinder {
    setCompiler(new JoeTWO_SICompiler())
}

class JoeTHREEModelFinder  extends JoeModelFinder {
    setCompiler(new JoeTHREECompiler())
}

class JoeTHREE_SIModelFinder  extends JoeModelFinder {
    setCompiler(new JoeTHREE_SICompiler())
}

class JoeFOURModelFinder  extends JoeModelFinder {
    setCompiler(new JoeFOURCompiler())
}

class JoeFOUR_SIModelFinder  extends JoeModelFinder {
    setCompiler(new JoeFOUR_SICompiler())
}
