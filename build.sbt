ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.3.4"

lazy val root = (project in file("."))
  .in(file("algorithm"))
  .enablePlugins(StainlessPlugin) // <-- Enabling Stainless verification on this module!
  .settings(
    name := "prime-numbers"
  )

libraryDependencies += "org.scalatest" %% "scalatest" % "3.3.0-SNAP4" % Test
