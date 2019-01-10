/*
 * Copyright (c) 2016, Amirhossein Vakili
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *    1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 *    2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package fortress.util;

/**
 * Created by Amirhossein Vakili.
 */
public class Timer {

    private long day, hour, minute, second, hsec;
    private long start;
    private String report;

    public Timer(){
        start = System.nanoTime();
    }

    public void set(){
        start = System.nanoTime();
    }

    public void stop(){
        long length = System.nanoTime();
        length = (length - start) / 10000000;
        hsec = length % 100;
        length /= 100;
        second = length % 60;
        length /= 60;
        minute = length % 60;
        length /= 60;
        hour = length % 60;
        length /= 60;
        day = length;
        report = "";
        if (day != 0)
            report = report + Long.toString(day) + "d ";
        if (hour != 0)
            report = report + Long.toString(hour) + "h ";
        if (minute != 0)
            report = report + Long.toString(minute) + "m ";
        report = report + Long.toString(second) + "." + Long.toString(hsec) + "s";
    }

    public String getReport() {
        return report;
    }
}
