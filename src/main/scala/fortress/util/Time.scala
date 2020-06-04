package fortress.util

class Milliseconds(val value: Int) extends AnyVal {
    def >(other: Milliseconds): Boolean = value > other.value
    def >=(other: Milliseconds): Boolean = value >= other.value
    def <(other: Milliseconds): Boolean = value < other.value
    def <=(other: Milliseconds): Boolean = value <= other.value
    def +(other: Milliseconds): Milliseconds = new Milliseconds(value + other.value)
    def -(other: Milliseconds): Milliseconds = new Milliseconds(value - other.value)
    
    def toNano: Nanoseconds = Nanoseconds(value * 1000000L)
}

object Milliseconds {
    def apply(value: Int): Milliseconds = new Milliseconds(value)
}

class Nanoseconds(val value: Long) extends AnyVal {
    
    def >(other: Nanoseconds): Boolean = value > other.value
    def >=(other: Nanoseconds): Boolean = value >= other.value
    def <(other: Nanoseconds): Boolean = value < other.value
    def <=(other: Nanoseconds): Boolean = value <= other.value
    def +(other: Nanoseconds): Nanoseconds = new Nanoseconds(value + other.value)
    def -(other: Nanoseconds): Nanoseconds = new Nanoseconds(value - other.value)
    
    def toMilli: Milliseconds = new Milliseconds((value / 1000000L).toInt)
    
    def prettyPrint: String = {
        val milliseconds: Long = value / (1000000)
        val justMillis: Long = milliseconds % 1000
        val wholeSeconds: Long = milliseconds / 1000
        val justSeconds: Long = wholeSeconds % 60
        val wholeMinutes: Long = wholeSeconds / 60
        val justMinutes: Long = wholeMinutes % 60
        val wholeHours: Long = wholeMinutes / 60
        val justHours: Long = wholeHours % 60
        
        var report = ""
        // Print hours
        val printHours: Boolean = justHours > 0
        if(justHours > 0) {
            report += justHours.toString + "h"
            report += " "
        }
        
        // Print minutes
        val printMinutes: Boolean = printHours || (justMinutes > 0)
        if(printHours && justMinutes < 10) {
            report += "0"
        }
        if(printMinutes) {
            report += justMinutes.toString + "m"
            report += " "
        }
        
        if(printMinutes && justSeconds < 10) {
            report += "0"
        }
        report += justSeconds.toString
        report += "."
        if(justMillis < 100) {
            report += "0"
        }
        if(justMillis < 10) {
            report += "0"
        }
        report += justMillis.toString
        report += "s"
        report
    }
}

object Nanoseconds {
    def apply(value: Long): Nanoseconds = new Nanoseconds(value)
}
