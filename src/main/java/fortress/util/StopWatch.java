package fortress.util;

import java.lang.IllegalStateException;

public class StopWatch {
    
    private long start;
    private long stop;
    private boolean running;
    
    public StopWatch() {
        this.start = -1;
        this.stop = -1;
        this.running = false;
    }
    
    public void start() {
        if(running) {
            throw new IllegalStateException();
        }
        start = System.nanoTime();
        running = true;
    }
    
    // Stops the timer and returns the elapsed time in nanoseconds
    public long stop() {
        if(!running) {
            throw new IllegalStateException();
        }
        stop = System.nanoTime();
        return stop - start;
    }
    
    public static String format(long nanoseconds) {
        // long length = nanoseconds / 10000000;
        // long hsec = length % 100;
        // length /= 100;
        // long second = length % 60;
        // length /= 60;
        // long minute = length % 60;
        // length /= 60;
        // long hour = length % 60;
        // length /= 60;
        // long day = length;
        // String report = "";
        // if (day != 0)
        //     report = report + Long.toString(day) + "d ";
        // if (hour != 0)
        //     report = report + Long.toString(hour) + "h ";
        // if (minute != 0)
        //     report = report + Long.toString(minute) + "m ";
        // report = report + Long.toString(second) + "." + Long.toString(hsec) + "s";
        // return report;
        
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
