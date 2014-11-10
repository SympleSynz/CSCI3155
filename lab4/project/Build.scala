import sbt._
import Keys._

object LabBuild extends Build {
  lazy val root = Project(id = "lab4",
                          base = file("."))

  lazy val grader = Project(id = "lab4-grader",
                            base = file("grader")) dependsOn(root)
}
