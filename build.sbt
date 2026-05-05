ThisBuild / scalaVersion := "2.13.18"
ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "org.leanlite"

val roaringBitmapVersion = "1.3.0"
lazy val graalvmNativeImageClasspath = taskKey[File]("Writes the runtime classpath used by GraalVM native-image")

lazy val root = (project in file(".")).settings(
  name := "raccoon-lang",
  Compile / mainClass := Some("com.raccoonlang.Main"),
  Compile / scalacOptions ++= Seq(
    "-deprecation",
    "-feature",
    "-Xfatal-warnings"
  ),
  Test / fork := true,
  libraryDependencies ++= Seq(
    "org.roaringbitmap" % "RoaringBitmap" % roaringBitmapVersion,
    "org.scalameta" %% "munit" % "0.7.29" % Test
    ),
  graalvmNativeImageClasspath := {
    val out = target.value / "graalvm" / "classpath.txt"
    val classpath = (Runtime / fullClasspath).value.files.map(_.getAbsolutePath).mkString(java.io.File.pathSeparator)
    IO.write(out, classpath + System.lineSeparator())
    streams.value.log.info(s"Wrote GraalVM native-image classpath to ${out.getAbsolutePath}")
    out
  }
  )
