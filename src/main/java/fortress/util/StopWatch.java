package fortress.util;

import java.lang.IllegalStateException;

public class StopWatch {
    
    private long start;
    private boolean running;
    
    public StopWatch() {
        this.start = -1;
        this.running = false;
    }
    
    public void startFresh() {
        start = System.nanoTime();
        running = true;
    }
    
    // Returns the elapsed time in nanoseconds
    public long elapsedNano() {
        if(!running) {
            throw new IllegalStateException();
        }
        long now = System.nanoTime();
        return now - start;
    }
    
    public static long millisToNano(int seconds) {
        return ((long)seconds) * 1000000L;
    }
    
    public static int nanoToMillis(long nanoseconds) {
        return (int) (nanoseconds / 1000000L);
    }
    
    public static String formatNano(long nanoseconds) {
        
        long milliseconds = nanoseconds / (1000000);
        long justMillis = milliseconds % 1000;
        long wholeSeconds = milliseconds / 1000;
        long justSeconds = wholeSeconds % 60;
        long wholeMinutes = wholeSeconds / 60;
        long justMinutes = wholeMinutes % 60;
        long wholeHours = wholeMinutes / 60;
        long justHours = wholeHours % 60;
        
        String report = "";
        // Print hours
        boolean printHours = justHours > 0;
        if(justHours > 0) {
            report += Long.toString(justHours) + "h";
            report += " ";
        }
        
        // Print minutes
        boolean printMinutes = printHours || (justMinutes > 0);
        if(printHours && justMinutes < 10) {
            report += "0";
        }
        if(printMinutes) {
            report += Long.toString(justMinutes) + "m";
            report += " ";
        }
        
        if(printMinutes && justSeconds < 10) {
            report += "0";
        }
        report += Long.toString(justSeconds);
        report += ".";
        if(justMillis < 100) {
            report += "0";
        }
        if(justMillis < 10) {
            report += "0";
        }
        report += Long.toString(justMillis);
        report += "s";
        return report;
        
    } 
    
}
