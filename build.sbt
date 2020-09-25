ThisBuild / version      := "0.1.0"
ThisBuild / scalaVersion := "2.13.2"
ThisBuild / organization := "ca.uwaterloo.watform"

// Antlr
enablePlugins(Antlr4Plugin)
antlr4Version in Antlr4 := "4.7.2"
antlr4PackageName in Antlr4 := Some("fortress.inputs")
antlr4GenListener in Antlr4 := false // default: true
antlr4GenVisitor in Antlr4 := true // default: false
antlr4TreatWarningsAsErrors in Antlr4 := true // default: false

// Scalatest
libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.0" % Test

// Command line tools
libraryDependencies += "org.rogach" %% "scallop" % "3.5.1"

// Use Java 10
javacOptions ++= Seq("-source", "10", "-target", "10")
scalacOptions += "-target:jvm-10"

// Sbt native packaging for creating zip file
enablePlugins(JavaAppPackaging)

// Disable documentation generation
sources in (Compile,doc) := Seq.empty
publishArtifact in (Compile, packageDoc) := false