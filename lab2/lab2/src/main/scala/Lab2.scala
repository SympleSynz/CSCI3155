object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._
  
  //Erik Eakins
  //Partner: Dan Matthews
  //Collaborator: Noah Dillon, Jessica Lynch, LA: David Baird


  /*
   * CSCI 3155: Lab 2
   */

  /*
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
  
  /* We represent a variable environment is as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */
  
  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }
  
  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(b) => if (b) 1 else 0
      case S(s) => try s.toDouble catch{case _:Throwable => Double.NaN}
      case Undefined => Double.NaN
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case S(s) => if (s == "") false else true
      case N(n) => if(n == 0 || n == -0 || n == Double.NaN) false else true
      case Undefined => false
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case B(b) => if (b) "true" else "false"
      case N(n) => "%s".format(n)
      case Undefined => "undefined"
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): Expr = eval(env, e)
    e match 
    {
      case Unary(Neg, e1) => N(-toNumber(eToVal(e1)))
      case Unary(Not, e1) => if(toBoolean(eToVal(e1)) == false) B(true) else B(false)
      case Binary(Plus, e1, e2) => 
        (e1,e2) match {
          case (S(s),e2) => S(toStr(eToVal(e1)) + toStr(eToVal(e2)))
          case (e1,S(s)) => S(toStr(eToVal(e1)) + toStr(eToVal(e2)))
          case (_,_) => N(toNumber(eToVal(e1)) + toNumber(eToVal(e2)))
          }
        
      case Binary(Minus, e1, e2) => N(toNumber(eToVal(e1)) - toNumber(eToVal(e2)))
      case Binary(Times, e1, e2) => N(toNumber(eToVal(e1)) * toNumber(eToVal(e2)))
      case Binary(Div, e1, e2) => N(toNumber(eToVal(e1)) / toNumber(eToVal(e2)))
      case Binary(Eq, e1, e2) => if(toNumber(eToVal(e1)) == toNumber(eToVal(e2))) B(true) else B(false)
      case Binary(Ne, e1, e2) => if(toNumber(eToVal(e1)) != toNumber(eToVal(e2))) B(true) else B(false)
      case Binary(Lt, e1, e2) => if(toNumber(eToVal(e1)) < toNumber(eToVal(e2))) B(true) else B(false)
      case Binary(Le, e1, e2) => if(toNumber(eToVal(e1)) <= toNumber(eToVal(e2))) B(true) else B(false)
      case Binary(Gt, e1, e2) => if(toNumber(eToVal(e1)) > toNumber(eToVal(e2))) B(true) else B(false)
      case Binary(Ge, e1, e2) => if(toNumber(eToVal(e1)) >= toNumber(eToVal(e2))) B(true) else B(false)
      case Binary(And, e1, e2) => 
        (e1,e2) match{
          case (S(s),S(s1)) => if(toBoolean(eToVal(e1))) B(toBoolean(eToVal(e2))) else B(toBoolean(eToVal(e1)))
          case (S(s),B(b)) => if(toBoolean(eToVal(e1))) eToVal(e2) else B(toBoolean(eToVal(e1)))
          case (B(b),S(s)) => if(toBoolean(eToVal(e1))) B(toBoolean(eToVal(e2))) else eToVal(e1)
          case (_,_) => if(toBoolean(eToVal(e1))) eToVal(e2) else eToVal(e1)
        }
      case Binary(Or, e1, e2) => 
        (e1,e2) match{
          case (B(b), e2) => if(b) B(b) else eToVal(e2)
          case (e1, B(b)) => if(b) B(b) else eToVal(e1)
          case (_,_) => eToVal(e1) 
          }
      
      case Binary(Seq, e1, e2) => eToVal(e1);eToVal(e2)
      case If(e1, e2, e3) => if(toBoolean(e1)) eToVal(e2) else eToVal(e3)
      case ConstDecl(x, e1, e2) => eval(extend(env, x, e1),e2)
      case Print(e1) => println(pretty(eToVal(e1))); Undefined
      case Var(x) => eToVal(get(env,x))
      case _ => e
    }
  }
    
  // Interface to run your interpreter starting from an empty environment.
  def eval(e: Expr): Expr = eval(emp, e)

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def eval(s: String): Expr = eval(Parser.parse(s))

 /* Interface to run your interpreter from the command-line.  You can ignore what's below. */ 
 def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }
    
    val expr = Parser.parseFile(file)
    
    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }
    
    if (debug) { println("Evaluating ...") }
    
    val v = eval(expr)
    
    println(pretty(v))
  }

}