# Lab 1: Dan Matthews & Erik Eakins

Include your writeup for the Lab 1 questions here. Use correct
Markdown markup. For more details, start with the article
https://help.github.com/articles/github-flavored-markdown


## Question 1: *Binding and Scope*

### (a) Consider the following Scala code:

```
	1	val pi = 3.14
	2	def circumference(r:Double): Double = {
	3		val pi = 3.14159
	4		2.0 * pi *r
	5	}
	6	def area(r:Double): Double = 
	7		pi * r * r
```

**The use of pi at line 4 is bound at which line?**
	
	pi on line 4 is bound by the declaration of val pi = 3.14159 on line 3 because of the scope at which pi was declared in 
	the function.  Since pi was re-declared using val on line 3, pi will be mapped to 3.14159 until the bracket that ends its 
	scope.

**The use of pi at line 7 is bound at which line?**
	
	pi on line 7 is bound by val pi = 3.14 on line 1 because pi was not declared with a new value within the scope of the 2nd
	function.  Essentially, for this function, when the program runs, it checks within the scope to see if pi was given a 
	value, and since it wasn't, it checks outside the scope (before the function) to see if it was declared then.

### (b) Consider the following Scala code:

```
	1	val x = 3
	2	def f(x:Int): Int =
	3		x match {
	4		case 0 => 0
	5		case x => {
	6			val y = x + 1
	7			({
	8				val x = y + 1
	9				y
	10			} * f(x-1))
	11		}
	12	}
	13	val y = x + f(x)
```

**The use of x at line 3 is bound at which line?**
	
	The x at line 3 is bound by the value x being passed into f() at line 2.  For line 3, x is defined as the function's lone 
	parameter. (Programming in Scala, 152)

**The use of x at line 6 is bound at which line?**

	At line 6, x is still bound by the function's lone parameter being passed in at line 2.  Only when x does not equal 0 (the
	cases in line 4 and 5), will line 6 execute, in which it holds the value that was passed into the function

**The use of x at line 10 is bound at which line?**

	On line 10, x that is being passed into f() is still bound by the lone parameter being passed into the function at line 2.
	The x declared on line 8 is in a different scope than the reference to x on line 10 (the {} tell us the scope).

**The use of x at line 13 is bound at which line?**

	The use of x on line 13 is outside the scope of the function f(), therefore x is actually bound to the value declaration 
	on line 1.

## Question 2: *Scala Basics: Typing*

###Consider the following code:
```
	1	def g(x:Int) = {
	2		val (a,b) = (1, (x,3))
	3		if (x == 0) (b, 1) else (b, a + 2)
	4	}
```
**Is the body of g well-typed if a valid return type is included into the code?**

	A well-typed code would basically be code that is consistent.  In this respect, if we included a valid return type, the
	code would be well-typed because the return type would always be true in both if and else situations.

**If so, give the return type of g and explain how you determined this type?**

For this explanation, first, give the types of names a and b.  Then, explain the body expression using the following format:
		
	e:o because
		e1:o1 because
			...
		e2:o2 because
			...

	1. A valid return type for the above code is: ((Int,Int), Int)
	2. (a,b) : (Int, (Int,Int)) because
			a : Int because 
				1 : Int
			b : (Int, Int) because
				x : Int
				3 : Int