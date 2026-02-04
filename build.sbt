ThisBuild / scalaVersion := "2.13.18"
ThisBuild / version := "0.1.0-SNAPSHOT"
ThisBuild / organization := "org.leanlite"

lazy val root = (project in file(".")).settings(
  name := "raccoon-lang",
  Compile / console / scalacOptions ++= Seq(
    "-deprecation",
    "-feature"
  ),
  Test / fork := true,
  libraryDependencies ++= Seq(
    "org.scalameta" %% "munit" % "0.7.29" % Test
  )
)
