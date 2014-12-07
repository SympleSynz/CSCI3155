import org.scalatest._
import jsy.lab5.ast._
import Lab5._

class Lab5Spec extends FlatSpec {
  
  "mapFirstDoWith" should "map the first element where f returns Some" in {
     val l1 = List(1, 2, -3, 4, -5)
     val gold1 = List(1, 2, 3, 4, -5)
     def dowith[W]: DoWith[W,List[Int]] = mapFirstWith[W,Int] { (i: Int) => if (i < 0) Some(doreturn(-i)) else None } (l1)
     assertResult((true,gold1)) { dowith(true) }
     assertResult((42,gold1)) { dowith(42) }
  }

  // Probably want to write some tests for castOk, typeInfer, substitute, and step.
  "DoNeg" should "negate values" in {
    val e = Unary(Neg, N(42))
    val (mp:Mem, ep: Expr) = step(e)(Mem.empty)
    assert(mp.isEmpty)
    assertResult(N(-42)) { ep }
  }
  "DoSeq" should "produce second element in sequence" in {
    val e = Binary(Seq, N(1), Binary(Plus, N(2), N(3)))
    val (mp:Mem, ep: Expr) = step(e)(Mem.empty)
    assert(mp.isEmpty)
    assertResult(Binary(Plus, N(2), N(3))) { ep }
  }
  "DoAssignVar" should "assign variable to value" in {
  	val e = Decl(MVar,"x",N(42.0),Assign(Var("x"),N(47.0)))
	val (mp:Mem, ep: Expr) = step(e)(Mem.empty)  
	val aref = ep match {
		case Assign(Unary(Deref, a@A(_)), N(47)) => Some(a)
		case _ => None
	}	
	val (mpp, epp: Expr) = step(ep)(mp)
	assertResult(N(47)) {
		mpp get (aref get) get
	}
	assertResult(N(47)) { epp }
  }

}
