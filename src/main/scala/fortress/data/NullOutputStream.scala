package fortress.data

import java.io.OutputStream

/** An output stream that writes to nowhere. */
class NullOutputStream extends OutputStream {
    override def write(b: Int): Unit = ()
}
