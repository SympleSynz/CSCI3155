object Lab1 extends jsy.util.JsyApplication {
  import jsy.lab1.ast._
  import jsy.lab1.Parser
  
  /*
   * CSCI 3155: Lab 1
   * Erik Eakins
   * 
   * Partner: Daniel Matthews
   * Collaborators: Piazza
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  /*
   * Example with a Unit Test
   * 
   * A convenient, quick-and-dirty way to experiment, especially with small code
   * fragments, is to use the interactive Scala interpreter.
   * 
   * To run a selection in the interpreter in Eclipse, highlight the code of interest
   * and type Ctrl+Shift+X (on Windows) or Cmd+Shift+X (on Mac).
   * 
   * Highlight the next few lines below to try it out.  The assertion passes, so
   * it appears that nothing happens.  You can uncomment the "bad test specification"
   * and see that a failed assert throws an exception.
   * 
   * You can try calling 'plus' with some arguments, for example, plus(1,2).  You
   * should get a result something like 'res0: Int = 3'.
   * 
   * As an alternative, the testPlus2 function takes an argument that has the form
   * of a plus function, so we can try it with different implementations.  For example,
   * uncomment the "testPlus2(badplus)" line, and you will see an assertion failure.
   * 
   * Our convention is that these "test" functions are testing code that are not part
   * of the "production" code.
   * 
   * While writing such testing snippets are convenient, it is not ideal.  For example,
   * the 'testPlus1()' call is run whenever this object is loaded, so in practice,
   * it should probably be deleted for "release".  A more robust way to maintain
   * unit tests is in a separate file.  For us, we use the convention of writing
   * tests in a file called LabXSpec.scala (i.e., Lab1Spec.scala for Lab 1).
   */
  
  def plus(x: Int, y: Int): Int = x + y
  def testPlus1() {
    assert(plus(1,1) == 2)
    //assert(plus(1,1) == 3) // bad test specification
  }
  testPlus1()

  def badplus(x: Int, y: Int): Int = x - y
  def testPlus2(plus: (Int, Int) => Int) {
    assert(plus(1,1) == 2)
  }
  //testPlus2(badplus)

  /* Exercises */

  def abs(n: Double): Double = //very straight forward answer
  if (n >= 0) n else -n
  def xor(a: Boolean, b: Boolean): Boolean = //this is fairly straight forward.  It's
    //basically following the truth table
    if(a) if (b) false else true else if (b) true else false
  def repeat(s: String, n: Int): String =  {require (n >= 0)
      n match{
    //by using require, we only deal with values greater and equal to 0
    //if we didn't use require, we could use the next line
      //case n if n < 0 => throw new IllegalArgumentException
      case 0 => "" //for no repeats
      case 1 => s //for 1 repeat
      case n if n > 1 => 
        s.concat(repeat(s, n-1)) //concat means that it will add the strings together
        //to itself.  Kinda like in python if you did s+= repeat(s,n-1)
      }
    }
  def sqrtStep(c: Double, xn: Double): Double = {
    xn - (((xn*xn)-c)/(2*xn))
    //calculate newton's method
  }

  def sqrtN(c: Double, x0: Double, n: Int): Double = {require(n>=0)//any negative number will throw an exception
    n match {
  //my base-case is that when n == 0, we return that initial guess
    case 0 => x0
    //here, we do our recursive call to sqrtstep which calculates a single iteration of Newton's method, and we reduce
    //the iterations by one
    case _ => sqrtN(c, sqrtStep(c,x0), n-1)
    } 
  }
  
  def sqrtErr(c: Double, x0: Double, epsilon: Double): Double = {require(epsilon > 0) //can't ever be less than neg or 0 if
    //taking the absolute value of a number
  if (abs((x0*x0)-c) < epsilon) //This is my exit strategy
      x0
  else //here we do recursion where we call sqrtStep to get a new x0 value
    sqrtErr(c,sqrtStep(c, x0), epsilon)
  }
  
  def sqrt(c: Double): Double = {
    require(c >= 0)
    if (c == 0) 0 else sqrtErr(c, 1.0, 0.0001)
  }
  
  /* Search Tree */
  
  sealed abstract class SearchTree
  case object Empty extends SearchTree
  case class Node(l: SearchTree, d: Int, r: SearchTree) extends SearchTree
  
  def repOk(t: SearchTree): Boolean = {
    def check(t: SearchTree, min: Int, max: Int): Boolean = t match {
      case Empty => true
      case Node(l, d, r) => 
      //since we are passing in tMin and tMax, that means whenever we go left, all nodes
        //must be greater than or equal to the minimum, and greater than the value of the
        //previous node because we passed d in as the max
        //which means that when we go right, all our values must be less than tmax, but
        //still greater or equal to the max value.  This ends up working out perfectly
        //for both going right and left
        check(l,min,d) && check(r, d, max) && (d >= min) && (d < max)
        //Only two places this fails is on an unbalanced tree where the root is Tmin and Tmin was placed to
        //the left and right of the root. And when Tmax is the root and a 2nd Tmax is placed to the left or right
    }
    check(t, Int.MinValue, Int.MaxValue)
  }
  
  def insert(t: SearchTree, n: Int): SearchTree = t match{
    case Empty => Node(Empty,n,Empty)
    case Node(l,d,r) =>{
      if (n >= d)//only two main conditions to deal with, if the node is empty, create
        //a new node, other than that, check the current node.  All values greater than
        //or equal to the current node, must go to the write.  Now, since we have to add
        //a link to the write, we are basically creating a brand new current Node that is
        //connected to the new Node with the new value
        Node(l,d,insert(r,n))
      else 
        Node(insert(l,n),d,r)//less than go left
    }
    
  }
  def deleteMin(t: SearchTree): (SearchTree, Int) = {
    require(t != Empty)
    (t: @unchecked) match {
      case Node(Empty, d, r) => (r, d)
      case Node(l, d, r) =>{
        val (l1, m) = deleteMin(l)
        (Node(l1,d,r),m)
      }
    }
  }
 
  def delete(t: SearchTree, n: Int): SearchTree = t match{
    case Empty => Empty
    case Node(Empty,d,Empty) => if(n == d) Empty else Node(Empty,d,Empty) //if matches and no children, return empty, otherwise
    //return the Node since the value is not in the tree
    case Node(Empty,d,r) => {//if greater than, traverse right
      if (n > d) Node(Empty,d,delete(r,n)) 
      else if (n < d) Node(Empty,d,r) //if less than, value not in tree, return Node
      else r //return the right leaf
    }
    case Node(l,d,Empty) => { //same as above except in reverse and for the left side
      if (n > d) Node(l,d,Empty)
      else if (n < d) Node(delete(l,n),d,Empty)
      else l
    }
    case Node(l,d,r) =>{ //this is where it gets tricky.  If less than, traverse left.  If greater than, traverse right
      //but if equal, we call deleteMin on the right side to replace the node we are about to delete
      if (n > d) Node(l,d,delete(r,n))
      else if (n < d) Node(delete(l,n),d,r)
      else {
        val (r1,m) = deleteMin(r)
        Node(l,m,r1)
      }
    }
    
  }

 
  /* JavaScripty */
  
  def eval(e: Expr): Double = e match {
    case N(n) => n //return the numerical value of the expression
    case Unary(Neg, e1) => if(eval(e1) >= 0) -eval(e1) else eval(e1)//if the exp is positive, then we return a negative 
    //number, if e1 is negative, then we negate and return the positive
    case Binary(Plus, e1, e2) => eval(e1) + eval(e2) //get the numerical expression through an eval call, then add the 
    //values together
    case Binary(Minus, e1, e2) => eval(e1) - eval(e2) //same as above, except we get the difference
    case Binary(Times, e1, e2) => eval(e1) * eval(e2) //same as above, except we get the multiplication
    case Binary(Div, e1, e2) => eval(e1) / eval(e2) //same as above, except we are doing division.  The eval takes care
    //of negative and positive infinity already as well as dividing into 0.
    case _ => throw new UnsupportedOperationException
  }
  
 // Interface to run your interpreter from a string.  This is convenient
 // for unit testing.
 def eval(s: String): Double = eval(Parser.parse(s))



 /* Interface to run your interpreter from the command-line.  You can ignore the code below. */ 
  
 def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }
    
    val expr = Parser.parseFile(file)
    
    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }
    
    if (debug) { println("Evaluating ...") }
    
    val v = eval(expr)
    
    println(v)
  }

}
