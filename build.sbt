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

// HTML test report
// libraryDependencies += "org.pegdown" % "pegdown" % "1.6.0" % Test
// testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-h", "target/test-reports")