ThisBuild / scalaVersion := "2.13.18"
ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "org.leanlite"

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
    "org.scalameta" %% "munit" % "0.7.29" % Test
  )
)

// Native binary subproject (reuses JVM main sources, no tests).
lazy val native = (project in file("native"))
  .enablePlugins(ScalaNativePlugin)
  .settings(
    name := "raccoon",
    Compile / mainClass := Some("com.raccoonlang.Main"),
    Compile / unmanagedSourceDirectories += file("src/main/scala"),
    Compile / scalacOptions ++= Seq(
      "-deprecation",
      "-feature"
    ),
    Test / sources := Seq.empty,
    Test / test := {}
  )
