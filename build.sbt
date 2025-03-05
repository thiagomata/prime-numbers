
ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "com.thiagomata"
ThisBuild / scalaVersion := "3.5.0"

name := "prime-numbers"
version := "0.0.0"

// sounds good does not work
//libraryDependencies += "ch.epfl.lara" % "stainless-dotty-plugin_3.5.0" % "0.9.8.9"

// forcing the jar load as alternative
unmanagedJars in Compile += baseDirectory.value / "lib" / "stainless-dotty-plugin-0.9.8.9.jar"


lazy val root = (project in file("."))
  .enablePlugins(StainlessPlugin)
  .settings(
    name := "prime-numbers"
  )


libraryDependencies += "org.scalatest" %% "scalatest" % "3.3.0-SNAP4" % Test

unmanagedResources in Compile := (unmanagedResources in Compile).value.filterNot {
  _.getPath.contains("stainless-library_3-0.9.8.9-SNAPSHOT-sources/META-INF/MANIFEST.MF")
}

artifactName in (Compile, packageBin) := { (sv: ScalaVersion, module: ModuleID, artifact: Artifact) =>
  s"${module.name}-${module.revision}.jar"
}

mainClass in Compile := Some("v1.div.DivMain")

import sbtassembly.AssemblyPlugin.autoImport._

//assemblyMergeStrategy in assembly := {
////  case x if x.startsWith("stainless/annotation") && x.contains("tasty") => MergeStrategy.discard
////  case x if x.startsWith("stainless/collection") && x.contains("tasty") => MergeStrategy.discard
////  case x if x.startsWith("stainless/covcollection") && x.contains("tasty") => MergeStrategy.discard
////  case x if x.startsWith("stainless/equations") && x.contains("tasty") => MergeStrategy.discard
////  case x if x.startsWith("stainless/io")  && x.contains("tasty")=> MergeStrategy.discard
////  case x if x.startsWith("stainless/lang") && x.contains("tasty") => MergeStrategy.discard
////  case x if x.startsWith("stainless/math") && x.contains("tasty") => MergeStrategy.discard
////  case x if x.startsWith("stainless/proof") && x.contains("tasty") => MergeStrategy.discard
////  case x if x.startsWith("stainless/util") && x.contains("tasty") => MergeStrategy.discard
//  case x if x.contains("stainless-dotty-plugin-0.9.8.9") => MergeStrategy.discard
//  case x => (assemblyMergeStrategy in assembly).value(x)
//}
//assemblyMergeStrategy in assembly := {
//  case "stainless/annotation/pure.tasty" => MergeStrategy.discard
//  case "stainless/covcollection/Option.tasty" => MergeStrategy.discard
//  case x => (assemblyMergeStrategy in assembly).value(x)
//}