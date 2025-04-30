import sbtassembly.AssemblyPlugin.autoImport.assembly

scalaVersion := "3.5.0"
crossScalaVersions := Seq("3.5.0")

//ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "com.thiagomata"
ThisBuild / scalaVersion := "3.5.0"

name := "prime-numbers"
version := "0.0.0"

enablePlugins(AssemblyPlugin)
enablePlugins(StainlessPlugin);
enablePlugins(JacocoPlugin)

jacocoExcludes := Seq(
  "stainless.*",
)

libraryDependencies += "org.scalatest" %% "scalatest" % "3.3.0-SNAP4" % Test

// sounds good does not work
//libraryDependencies += "ch.epfl.lara" % "stainless-dotty-plugin_3.5.0" % "0.9.8.9"

// forcing the jar load as alternative
//unmanagedJars in Compile += baseDirectory.value / "lib" / "stainless-dotty-plugin-0.9.8.9.jar"
unmanagedJars in Compile += baseDirectory.value / "project" / "lib" / "sbt-stainless.jar"
unmanagedJars in Compile += baseDirectory.value / "project" / "lib" / "stainless-library.jar"

lazy val root = (project in file("."))
  .enablePlugins(StainlessPlugin)
  .settings(
    name := "prime-numbers",
    assembly / mainClass := Some("v1.div.DivMain"),
  )


 libraryDependencies += "org.scalatest" %% "scalatest" % "3.3.0-SNAP4" % Test

//unmanagedResources in Compile := (unmanagedResources in Compile).value.filterNot {
//  _.getPath.contains("stainless-library_3-0.9.8.9-SNAPSHOT-sources/META-INF/MANIFEST.MF")
//}


mainClass in Compile   := Some("v1.div.DivMain")
mainClass in assembly  := Some("v1.div.DivMain")

artifactName in (Compile, packageBin) := { (sv: ScalaVersion, module: ModuleID, artifact: Artifact) =>
  s"${module.name}-${module.revision}.jar"
}