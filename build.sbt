ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.5.2"

lazy val root = (project in file("."))
  .enablePlugins(StainlessPlugin)
  .settings(
    name := "prime-numbers"
  )

libraryDependencies += "org.scalatest" %% "scalatest" % "3.3.0-SNAP4" % Test
