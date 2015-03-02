import org.scalatest._
import jsy.lab3.ast._
import Lab3._

class FunctionCallSpec extends FlatSpec {

  "Functions" should "be considered values" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Var(x))
    val e2 = Function(Some(f), x, Var(x))
    assert(evaluate(e1) == e1)
    assert(evaluate(e2) == e2)
  } 
  
  "Call" should "evaluate a function using big-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = evaluate(Call(e1, e2))
    assert(e3 === N(3))
  }

  "Call" should "handle recursive functions using big-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), Binary(Minus, Var(x), N(1)))))
    val e1 = Function(Some(f), x, fbody)
    val e2 = N(3)
    val e3 = evaluate(Call(e1, e2))
    assert(e3 === N(6))
  } 

  
  "Call" should "evaluate a function using small-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === N(3))
  }

  "Call" should "handle recursive functions using small-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), Binary(Minus, Var(x), N(1)))))
    val e1 = Function(Some(f), x, fbody)
    val e2 = N(3)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === N(6))
  }

  "Call" should "handle small and big step differently" in {
    val f = "f"
    val x = "x"
    val r = "r"
    val g = "g"
    val y = "y"
    val h = "h"
    val plus = "plus"
    val e1 = ConstDecl(x,N(2.0),ConstDecl(r,Binary(Plus,Call(Function(None,x,N(3.0)),N(4.0)),Var(x)),Binary(Seq,Print(Var(r)),ConstDecl(x,N(2.0),ConstDecl(g,Function(None,y,Var(x)),ConstDecl(h,Function(None,x,Call(Var(g),N(3.0))),Binary(Seq,Print(Call(Var(h),N(4.0))),ConstDecl(x,N(42.0),ConstDecl(plus,Function(None,x,Function(None,y,Binary(Plus,Var(x),Var(y)))),Print(Call(Call(Var(plus),N(3.0)),N(4.0))))))))))))
    assert (evaluate(e1) === Undefined)
    assert (iterateStep(e1) === Undefined) 
  }
}
