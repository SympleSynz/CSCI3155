# Lab 2

Refer to the lab handout lab2.pdf for details about the assignment.  This file provides some information to help you get started with setting up your development environment for the labs.


## Important Files

```
.
├── Lab2.md
├── README.md (this file)
├── build.sbt
├── grader
│   ├── Lab2Grader.scala
│   └── build.sbt
├── lib
│   ├── liblab2.jar
│   └── scalatest_2.10-2.0.jar
├── src
│   ├── main
│   │   └── scala
│   │       ├── Lab2.scala (fill in this implementation template!)
│   │       └── jsy
│   │           └── lab2
│   │               └── ast.scala
│   └── test
│       └── scala
│           └── Lab2Spec.scala (add unit tests!)
└── testjsy  (some JavaScripty test cases)
    ├── test01_arith.jsy
    └── test02_divbyzero.jsy
```

## Scala Development Tools

We will use a slightly older version of [Scala](http://www.scala-lang.org/) (at least for Lab 2), namely 2.10.3. The provided build.sbt uses this dependency.

The TAs will support [Scala IDE](http://scala-ide.org/) for [Eclipse](http://www.eclipse.org/) for Scala development in this course.  You are welcome to use any development environment, but we may not be able answer questions in your particular environment.

To install Scala IDE, first [download](http://www.eclipse.org/downloads/) and install Eclipse.  The standard package is sufficient.  For Fall 2014, we suggest installing Eclipse Kepler (the latest supported version).  Then, follow the [directions](http://scala-ide.org/download/current.html) for installing Scala IDE.

### Eclipse Import

To import the Lab 1 project files into Eclipse, go to

    File > Import > Existing Projects into Workspace (under General)

and then select

    Select archive file:

and browse to the lab2.zip that you downloaded from the course website.

### Command-Line Tools

While not required if you have installed Scala IDE, you may also want to install the command-line Scala compiler and tools.  If you would like to build the project on the command-line, you should install [sbt](http://www.scala-sbt.org/).  Scala and sbt is available in many OS-specific package managers.

For your convenience, an sbt script (build.sbt) is included.  You can issue the following commands to compile, run and test your code:

    $ sbt run
    
runs your project (after compiling).

    $ sbt clean

deletes the previous compilation.

It is often convenient to run sbt interactively

    $ sbt
    
and then run via

    > run

at the sbt prompt.

### Scala Interpreter

From the command-line, you can start the scala interpreter using the command

    $ scala

and can import the functions in your lab in the following way

    scala> import Lab2._

Note that you will need to run the scala interpreter in the same directory as the compiled version (lab2/bin/).

In Scala IDE, you can start a Scala interpreter with the project files available by selecting

    Window > Show View > Scala Interpreter

 
## ScalaTest

We will be using the [ScalaTest](http://www.scalatest.org/) framework for unit testing.  Using this framework, we practice test-driven development (TDD), a standard practice in industry.

We suggest you install the [ScalaTest plugin](http://www.scalatest.org/user_guide/using_scalatest_with_eclipse) for Scala IDE.

You do not need to explicitly download ScalaTest.

We provide some unit tests in Lab2Spec.scala to drive your implementation.  To run tests, right-click on the file and select

    Run As > ScalaTest - File
    
You can also run tests via

    $ sbt test


## JavaScripty Interpreter

You can run your JavaScripty interpreter with a file (e.g., tests in testjsy/) in Eclipse by right-clicking on Lab2.scala by setting up a Run Configuration:

    Run As > Run Configuration ...

For quick experimentation, it is more convenient to use the Scala Interpreter window.

