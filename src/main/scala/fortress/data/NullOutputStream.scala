package fortress.data

import java.io.OutputStream

class NullOutputStream extends OutputStream {
    override def write(b: Int): Unit = ()
}
