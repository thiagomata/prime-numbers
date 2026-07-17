import sbtassembly.AssemblyPlugin.autoImport.{assembly, assemblyExcludedJars}

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

// The Stainless SBT plugin is loaded from project/lib by SBT itself.
// Application sources only need the Stainless library on their compile/runtime
// classpath; adding the SBT plugin jar here leaks build tooling into the app jar.
Compile / unmanagedJars += baseDirectory.value / "project" / "lib" / "stainless-library.jar"

lazy val root = (project in file("."))
  .enablePlugins(StainlessPlugin)
  .settings(
    name := "prime-numbers",
    assembly / mainClass := Some("v1.chapter2.div.DivMain"),
  )


libraryDependencies += "org.scalatest" %% "scalatest" % "3.3.0-SNAP4" % Test

//unmanagedResources in Compile := (unmanagedResources in Compile).value.filterNot {
//  _.getPath.contains("stainless-library_3-0.9.8.9-SNAPSHOT-sources/META-INF/MANIFEST.MF")
//}


mainClass in Compile   := Some("v1.chapter2.div.DivMain")
mainClass in assembly  := Some("v1.chapter2.div.DivMain")

assembly / assemblyExcludedJars := {
  // Keep stainless-library.jar available for compilation and verification, but
  // do not feed the physical jar to assembly. The Stainless plugin/compiler path
  // already places the runtime classes in target/classes, so including the jar
  // again produces duplicate stainless/** entries in the fat jar.
  val classpath = (assembly / fullClasspath).value
  classpath.filter(_.data.getName == "stainless-library.jar")
}

artifactName in (Compile, packageBin) := { (sv: ScalaVersion, module: ModuleID, artifact: Artifact) =>
  s"${module.name}-${module.revision}.jar"
}

lazy val spark = (project in file("spark"))
  .settings(
    name := "prime-numbers-spark",
    scalaVersion := "2.13.15",
    libraryDependencies ++= Seq(
      "org.apache.spark" %% "spark-core" % "3.5.1",
      "org.apache.spark" %% "spark-sql"  % "3.5.1",
      "org.scalatest"    %% "scalatest"  % "3.2.18" % Test
    ),
    assembly / mainClass := Some("v1.chapter8.SparkSieveRunner"),
    run / fork := true,
    run / javaOptions ++= Seq(
      "--add-opens=java.base/sun.nio.ch=ALL-UNNAMED",
      "--add-opens=java.base/java.lang=ALL-UNNAMED",
      "--add-opens=java.base/java.lang.invoke=ALL-UNNAMED",
      "--add-opens=java.base/java.io=ALL-UNNAMED",
      "--add-opens=java.base/java.net=ALL-UNNAMED",
      "--add-opens=java.base/java.nio=ALL-UNNAMED",
      "--add-opens=java.base/java.util=ALL-UNNAMED",
      "--add-opens=java.base/java.util.concurrent=ALL-UNNAMED",
      "--add-opens=java.base/java.util.concurrent.atomic=ALL-UNNAMED",
      "--add-opens=java.base/sun.security.action=ALL-UNNAMED"
    ),
    Test / fork := true,
    Test / javaOptions ++= Seq(
      "--add-opens=java.base/sun.nio.ch=ALL-UNNAMED",
      "--add-opens=java.base/java.lang=ALL-UNNAMED",
      "--add-opens=java.base/java.lang.invoke=ALL-UNNAMED",
      "--add-opens=java.base/java.io=ALL-UNNAMED",
      "--add-opens=java.base/java.net=ALL-UNNAMED",
      "--add-opens=java.base/java.nio=ALL-UNNAMED",
      "--add-opens=java.base/java.util=ALL-UNNAMED",
      "--add-opens=java.base/java.util.concurrent=ALL-UNNAMED",
      "--add-opens=java.base/java.util.concurrent.atomic=ALL-UNNAMED",
      "--add-opens=java.base/sun.security.action=ALL-UNNAMED"
    ),
    Test / classLoaderLayeringStrategy := ClassLoaderLayeringStrategy.Flat
  )
