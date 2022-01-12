ThisBuild / version      := "0.1.0"
ThisBuild / scalaVersion := "2.13.2"
ThisBuild / organization := "ca.uwaterloo.watform"



lazy val root = (project in file("."))
    .aggregate(fortress, fortressDebug)

lazy val fortress = (project in file("cli"))
    .aggregate(fortressCore)
    .dependsOn(fortressCore)
    .enablePlugins(JavaAppPackaging) // Sbt native packaging for creating zip file
    .settings(
        name := "Fortress",
        // Dependencies
        libraryDependencies += "org.rogach" %% "scallop" % "3.5.1" // Command line tools
    )

lazy val fortressDebug = (project in file("debug"))
    .aggregate(fortressCore)
    .dependsOn(fortressCore)
    .enablePlugins(JavaAppPackaging) // Sbt native packaging for creating zip file
    .settings(
        name := "FortressDebug",
        // Dependencies
        libraryDependencies += "org.rogach" %% "scallop" % "3.5.1" // Command line tools
    )

lazy val fortressCore = (project in file("core"))
    .enablePlugins(JavaAppPackaging) // Sbt native packaging for creating zip file
    .enablePlugins(Antlr4Plugin)
    .settings(
        name := "FortressCore",
        // Use Java 10
        javacOptions ++= Seq("-source", "10", "-target", "10"),
        scalacOptions += "-target:jvm-10",
        // Antlr
        antlr4Version in Antlr4 := "4.7.2",
        antlr4PackageName in Antlr4 := Some("fortress.inputs"),
        antlr4GenListener in Antlr4 := false, // default: true
        antlr4GenVisitor in Antlr4 := true, // default: false
        antlr4TreatWarningsAsErrors in Antlr4 := true, // default: false
        // Dependencies
        libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.0" % Test, // Scala test
        libraryDependencies += "org.scala-lang.modules" %% "scala-parallel-collections" % "1.0.0", // Parallel collections
        // Disable documentation generation
        sources in (Compile,doc) := Seq.empty,
        publishArtifact in (Compile, packageDoc) := false
    )