ThisBuild / scalaVersion := "2.13.18"
ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "org.leanlite"

val roaringBitmapVersion = "1.3.0"
lazy val runtimeClasspath = taskKey[File]("Writes the runtime classpath for tools that launch the application")
lazy val validate = taskKey[Unit]("Checks formatting and runs the full test suite")

lazy val root = (project in file(".")).settings(
  name := "raccoon-lang",
  Compile / mainClass := Some("com.raccoonlang.Main"),
  Compile / scalacOptions ++= Seq(
    "-deprecation",
    "-feature",
    "-Wunused",
    "-Xfatal-warnings"
  ),
  Test / fork := true,
  // Forked tests get their own JVM, so the diagnostic-snapshot regeneration switch has to be handed across.
  Test / javaOptions ++= sys.props.get("raccoon.diagnostics.regenerate").map(v => s"-Draccoon.diagnostics.regenerate=$v"),
  libraryDependencies ++= Seq(
    "org.roaringbitmap" % "RoaringBitmap" % roaringBitmapVersion,
    "org.scalameta" %% "munit" % "0.7.29" % Test
    ),
  runtimeClasspath := {
    val out = target.value / "runtime-classpath.txt"
    val classpath = (Runtime / fullClasspath).value.files.map(_.getAbsolutePath).mkString(java.io.File.pathSeparator)
    IO.write(out, classpath + System.lineSeparator())
    streams.value.log.info(s"Wrote runtime classpath to ${out.getAbsolutePath}")
    out
  },
  validate := Def.sequential(scalafmtCheckAll, Test / test).value
  )
