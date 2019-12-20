# Overview

This directory contains examples of main programs that use the fortress library.

## Running Fortress in Your Project
1. Follow the steps for building Fortress.
2. Copy `build/distributions/fortress-2.0.tar` or `build/distributions/fortress-2.0.zip` (both archives contain the same files) to an appropriate location, such as a `libs` folder for your project. 
3. Unzip the archive.
4. When compiling and running, ensure that the files from this archive are in your Java `classpath`.
    * For example, if the files are in the `libs` directory of your project, you can add `-cp ".:libs/fortress-2.0/*"` to `javac`, which says to look for class files in current directory and also jars in the libs directory. 
5. When running, ensure that the `libz3java.dylib` or `libz3java.so` file from this archive (usually in the z3 directory) is in your `java.library.path`.
    * For example, if `libz3java.dylib` is in the `libs` directory, you can add `-Djava.library.path="libs/fortress-2.0"` to your call to `java`.
    * If this is not done correctly, a `java.lang.UnsatisfiedLinkError` may be raised at runtime.


## Example: Sudoko.java

- Create the Sudoko puzzle of size 4 (i.e., 4 numbers,  2x2 squares
- Solve it
- compile using "javac -cp '.:mylibs/fortress-2.0/*' Sudoku.java"
- run using "java -cp '.:mylibs/fortress-2.0/*' -Djava.library.path="libs/fortress-2.0" Sudoku
- 

