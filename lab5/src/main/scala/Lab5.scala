object Lab5 extends jsy.util.JsyApplication {
  import jsy.lab5.ast._
  import jsy.lab5._
  
  /*
   * CSCI 3155: Lab 5
   * Erik Eakins
   * 
   * Partner: Olivia Abrant
   * Collaborators: Michelle Soult, Jessica Lynch, Noah Dillon, Alok Joshi, Andrew Gordon, Catherine Dewerd
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
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
  
  /*** Helper: mapFirst to DoWith ***/
  
  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](f: A => Option[DoWith[W,A]])(l: List[A]): DoWith[W,List[A]] = l match 
  {
    case Nil => doreturn(l) //this is a function within DoWith that returns l without applying anything to it, which is good since the list is nil
    case h :: t => f(h) match //We need to match on the element of h
    {
      case None => mapFirstWith(f)(t).map((newList: List[A]) => (h::newList)) //if h returns None, then we need to continue to cycle through mapFirstWith
      //until we do find a value that satisfies f
      case Some(withhp) =>  withhp.map((newValueMapped: A) => (newValueMapped::t)) //This is when we find an element that satisfies f, we use the map
      //function since it is a DoWith function and mapFirstWith expects a DoWith returned.  This will map the new value returned from f into the list
      //and stop there, as well as returning W since we did not change anything to W, and that is our input-output state
    }
  }

  /*** Casting ***/
  
  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match 
  {
    case (TNull, TObj(_)) => true
    case (_, _) if (t1 == t2) => true
    case (TObj(fields1), TObj(fields2)) => 
      val checkUp = fields1.forall
      {
        case (str, ty) => if (ty == None) true else fields2.get(str) match 
        {
          case None => false 
          case Some(ty2) => castOk(ty,ty2)
        }
      }
      val checkDown = fields2.forall
      {
        case (str, ty) => if (ty == None) true else fields1.get(str) match 
        {
          case None => false 
          case Some(ty2) => castOk(ty,ty2)
        }
      }
      checkUp || checkDown
    case (TInterface(tvar, t1p), _) => castOk(typSubstitute(t1p, t1, tvar), t2)
    case (_, TInterface(tvar, t2p)) => castOk(t1, typSubstitute(t2p, t2, tvar))
    case _ => false
  }
  
  /*** Type Inference ***/
  
  def hasFunctionTyp(t: Typ): Boolean = t match 
  {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  } 
    
  def mut(m: PMode): Mutability = m match 
  {
    case PName => MConst
    case PVar | PRef => MVar
  }
  
  def typeInfer(env: Map[String,(Mutability,Typ)], e: Expr): Typ = 
  {
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw new StaticTypeError(tgot, e1, e)

    e match 
    {
      case Print(e1) => typ(e1); TUndefined
      //TypeNumber
      case N(_) => TNumber
      //TypeBool
      case B(_) => TBool
      //TypeUndefined
      case Undefined => TUndefined
      //TypeString
      case S(_) => TString
      //TypeVar
      case Var(x) =>
        val (_, t) = env(x)
        t
      //TypeNeg
      case Unary(Neg, e1) => typ(e1) match 
      {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      //TypeNot
      case Unary(Not, e1) => typ(e1) match 
      {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      //TypeArith
      case Binary(Plus, e1, e2) => typ(e1) match 
      {
        case TNumber => typ(e2) match 
        {
          case TNumber => TNumber
          case tgot => err(tgot, e2)
        }
        //TypePlusString
        case TString => typ(e2) match 
        {
          case TString => TString
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      //TypeArith
      case Binary(Minus|Times|Div, e1, e2) => typ(e1) match 
      {
        case TNumber => typ(e2) match 
        {
          case TNumber => TNumber
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      //TypeEquality
      case Binary(Eq|Ne, e1, e2) => typ(e1) match 
      {
        case t1 if !hasFunctionTyp(t1) => typ(e2) match 
        {
          case t2 if (t1 == t2) => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => typ(e1) match 
      {
        //TypeIneqaulityNumber
        case TNumber => typ(e2) match 
        {
          case TNumber => TBool
          case tgot => err(tgot, e2)
        }
        //TypeInequalityString
        case TString => typ(e2) match 
        {
          case TString => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      //TypeAndOr
      case Binary(And|Or, e1, e2) => typ(e1) match 
      {
        case TBool => typ(e2) match 
        {
          case TBool => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      //TypeSeq
      case Binary(Seq, e1, e2) => typ(e1); typ(e2)
      //TypeIf
      case If(e1, e2, e3) => typ(e1) match 
      {
        case TBool =>
          val (t2, t3) = (typ(e2), typ(e3))
          if (t2 == t3) t2 else err(t3, e3)
        case tgot => err(tgot, e1)
      }
      //TypeObject
      case Obj(fields) => TObj(fields map { case (f,t) => (f, typ(t)) })
      //TypeGetField
      case GetField(e1, f) => typ(e1) match 
      {
        case TObj(tfields) if (tfields.contains(f)) => tfields(f)
        case tgot => err(tgot, e1)
      } 
      
      case Function(p, paramse, tann, e1) => 
      {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        //TypeRecFunction
        //TypeFunctionAnn
        val env1 = (p, tann) match 
        {
          case (Some(f), Some(rt)) =>
            val tprime = TFunction(paramse, rt)
            env + (f -> (MConst, tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with the parameters.
        val env2 = paramse match 
        {
          //left does not handle mutability
          //TypeFunction
          case Left(params) => params.foldLeft(env1) ((environment, tup) => tup match 
          {
            case (str, ty) => environment + (str -> (MConst, ty))
          })
          //right handled mutability
          //TypeFunctionMode
          case Right((mode,x,t)) => mode match 
          {
          //There are three different modes that can be passed, therefore, that determines what mutability is used
            case PName => env1 + (x -> (MConst, t))
            case PVar => env1 + (x -> (MVar, t))
            case PRef => env1 + (x -> (MVar, t))
          }
        }
        // Infer the type of the function body
        //TypeFunctionAnnMode
        //TypeRecFunctionMode
        val t1 = typeInfer(env2, e1)
        tann foreach { rt => if (rt != t1) err(t1, e1) };
        TFunction(paramse, t1)
      }
      //TypeCall
      //TypeCallNameVar
      //TypeCallRef
      case Call(e1, args) => typ(e1) match 
      {
        case TFunction(Left(params), tret) if (params.length == args.length) => 
        {
          (params, args).zipped.foreach 
          {
            (paramsX, argsY) => (paramsX, argsY) match 
            {
              case ((str, ty), ta) => if (ty != typ(ta)) err(ty, ta)
            }
          }
          tret
        }
        case tgot @ TFunction(Right((mode,_,tparam)), tret) => mode match 
        {
          case PRef => args match
          {
            case h::Nil => if (typ(h) == tparam && isLExpr(h)) tret else err(tgot, e1)
            case _ => err(tgot, e1)
          }
          case _ => args match
          {
            case h::Nil => if (typ(h) == tparam) tret else err(tgot, e1)
            case _ => err(tgot, e1)
          }
        }      
        case tgot => err(tgot, e1)
      }
      /*** Fill-in more cases here. ***/
      //TypeDecl
      case Decl(mut,x,e1,e2) => typeInfer(env + (x -> (mut, typ(e1))),e2)
      //TypeNull
      case Null => TNull
      //TypeCast
      case Unary(Cast(t),e1) => if (castOk(typ(e1),t)) t else err(typ(e1),e1)
      //TypeAssignVar
      case Assign(e1,e2) => e1 match 
      {
        case Var(x) => env.get(x) match
        {
            case None => err(typ(e1),e1)
            case Some((MConst,_)) => err(typ(e1),e1)
            case Some((MVar, t)) => if (t == typ(e2)) t else err(typ(e1),e1)
            case _ => err(typ(e1),e1)
        }
        //TypeAssignField
        case GetField(e3, f) => typ(e3) match 
        {
          case TObj(tfields) => tfields.get(f) match 
          {
            case None => err(typ(e3), e3)
            case Some(t) => if (t != typ(e2)) err(t, e1) else t
          }
          case _ => err(typ(e1), e1) 
        }
        case _ => err(typ(e1), e1)
      }
      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }
  
  /*** Small-Step Interpreter ***/
  
  /* Do the operation for an inequality. */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    ((v1, v2): @unchecked) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case (N(n1), N(n2)) =>
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }
  
  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = 
  {
    def subst(e: Expr): Expr = substitute(e, esub, x)
    val ep: Expr = avoidCapture(freeVars(esub),e)
    ep match 
    {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else e
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
      case Function(p, paramse, retty, e1) => p match 
      {
        case Some(a) => paramse match 
        {
          case Left(params) => val e1p = 
            if (params.exists((t1:(String,Typ))=> t1._1 != x) && a != x) subst(e1)
            else e1
            Function(p, Left(params), retty, e1p)
          case Right((mode, str, ty)) => 
            if (str != x && a != x) Function(p, Right((mode, str, ty)), retty, subst(e1))
            else Function(p, Right((mode, str, ty)), retty, e1)
        }
        case None => paramse match 
        {
          case Left(params) => val e1p =
            if (params.exists((t1:(String,Typ))=> t1._1 != x)) subst(e1)
            else e1
            Function(p, Left(params), retty, e1p)
          case Right((mode, str, ty)) =>
            if (str != x) Function(p, Right((mode, str, ty)), retty, subst(e1))
            else Function(p, Right((mode, str, ty)), retty, e1)
        }
      }
      
      case Call(e1, args) => Call(subst(e1), args map subst)
      case Obj(fields) => Obj(fields map { case (fi,ei) => (fi, subst(ei)) })
      case GetField(e1, f) => GetField(subst(e1), f)
      case Assign(e1, e2) => Assign(subst(e1), subst(e2))
      case InterfaceDecl(tvar, t, e1) => InterfaceDecl(tvar, t, subst(e1))
    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))
    
    /*** Helpers for Call ***/
    
    def stepIfNotValue(e: Expr): Option[DoWith[Mem,Expr]] = if (isValue(e)) None else Some(step(e))
    
    /* Check whether or not the argument expression is ready to be applied. */
    def argApplyable(mode: PMode, arg: Expr): Boolean = mode match {
      case PVar => isValue(arg)
      case PName => true
      case PRef => isLValue(arg)
    }

    /*** Body ***/
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => for (m <- doget) yield { println(pretty(m, v1)); Undefined }
      case Unary(Neg, N(n1)) => doreturn( N(- n1) )
      case Unary(Not, B(b1)) => doreturn( B(! b1) )
      case Binary(Seq, v1, e2) if isValue(v1) => doreturn( e2 )
      case Binary(Plus, S(s1), S(s2)) => doreturn( S(s1 + s2) )
      case Binary(Plus, N(n1), N(n2)) => doreturn( N(n1 + n2) )
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(inequalityVal(bop, v1, v2)) )
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 == v2) )
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 != v2) )
      case Binary(And, B(b1), e2) => doreturn( if (b1) e2 else B(false) )
      case Binary(Or, B(b1), e2) => doreturn( if (b1) B(true) else e2 )
      case Binary(Minus, N(n1), N(n2)) => doreturn( N(n1 - n2) )
      case Binary(Times, N(n1), N(n2)) => doreturn( N(n1 * n2) )
      case Binary(Div, N(n1), N(n2)) => doreturn( N(n1 / n2) )
      case If(B(b1), e2, e3) => doreturn( if (b1) e2 else e3 )
      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) =>
        Mem.alloc(Obj(fields)) map {(a:A) => a:Expr}
      case GetField(a @ A(_), f) =>
      {  
        doget.map((m: Mem) => m.get(a) match 
        {
          case Some(Obj(fields)) => fields.get(f) match 
          {
            case Some(e1) => e1
            case _ => throw StuckError(e)
          }
          case _ => throw StuckError(e)
        })
      }   
      case Call(v1, args) if isValue(v1) =>
      {  
        def substfun(e1: Expr, p: Option[String]): Expr = p match 
        {
          case None => e1
          case Some(x) => substitute(e1, v1, x)
        }
        (v1, args) match 
        {
          /*** Fill-in the DoCall cases, the SearchCall2, the SearchCallVar, the SearchCallRef  ***/
          case (Function(p, paramse, retty, e1), arg::l) => paramse match 
          {
            //DoCall & DoCallRec
            case Left(params) if (args.forall(x => isValue(x)) && args.length == params.length) => 
            {
              val e1p = (params, args).zipped.foldRight(e1)
              {
                (paramTuple, exp) => paramTuple match 
                {
                  case ((param_name, _), expressions) => substitute(exp, expressions, param_name)
                }
              }
              doreturn(substfun(e1p, p))
              /*
              p match 
              {
                case None => doreturn(e1p)
                case Some(x1) => doreturn(substitute(e1p,v1,x1))
              }*/
            }
            //SearchCall2
            case Left(params) => for (argsp <- mapFirstWith(stepIfNotValue)(args)) yield Call(v1, argsp)
            //DoCallVar & DoCallRec
            case Right((PVar, x, f)) if (argApplyable(PVar, arg)) =>
              Mem.alloc(arg) map {a => substfun(substitute(e1, Unary(Deref, a), x), p)}  
            //SearchCallVar
            case Right((PVar, x, f)) => for (argsp <- step(arg)) yield Call(v1, argsp::Nil)
            //DoCallRef & DoCallRefRec
            case Right((PRef, x, f)) if (argApplyable(PRef, arg)) => doreturn(substfun(substitute(e1,arg, x), p))
            //SearchCallRef
            case Right((PRef, x, f)) => if (!isLValue(arg)) for (argsp <- step(arg)) yield Call(v1, argsp::Nil) else throw StuckError(e)
            //DoCallName & DoCallNameRec
            case Right((PName, x, f)) if (argApplyable(PName, arg)) => doreturn(substfun(substitute(e1, arg, x), p))
            case _ => throw StuckError(e)
          }
          case _ => throw StuckError(e)
        }
      }
      case Decl(MConst, x, v1, e2) if isValue(v1) => doreturn(substitute(e2, v1, x))  
      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        Mem.alloc(v1) map {a => substitute(e2, Unary(Deref,a), x)}

      //DoAssignGetField
      case Assign(GetField(a @ A(_), f), v) if isValue(v) => 
        for (_ <- domodify 
          { (m: Mem) => 
            { 
              if (m.contains(a)) 
              {
                val objForField = m(a)
                val updatedField = objForField match 
                {
                  case Obj(fields) => Obj(fields + (f -> (v)))
                  case _ => throw StuckError(e)
                }
                m + (a -> updatedField)
              }
              else m
            }
          })
        yield v

      //DoAssignVar
      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        for (_ <- domodify { (m: Mem) => (m + (a -> v)) : Mem }) yield v
        
      /*** Fill-in more Do cases here. ***/
      case Unary(Deref, a@A(_)) => doget.map((m: Mem) => m.apply(a))
      //DoCast
      case Unary(Cast(e1), v) => if (v == Null) doreturn(Null) else doreturn(v)

      /* Base Cases: Error Rules */
      /*** Fill-in cases here. ***/
        
      /* Inductive Cases: Search Rules */
      case Print(e1) =>
        for (e1p <- step(e1)) yield Print(e1p)
      case Unary(uop, e1) =>
        for (e1p <- step(e1)) yield Unary(uop, e1p)
      case Binary(bop, v1, e2) if isValue(v1) =>
        for (e2p <- step(e2)) yield Binary(bop, v1, e2p)
      case Binary(bop, e1, e2) =>
        for (e1p <- step(e1)) yield Binary(bop, e1p, e2)
      case If(e1, e2, e3) =>
        for (e1p <- step(e1)) yield If(e1p, e2, e3)
      //SearchObject
      case Obj(fields) => fields find { case (_, ei) => !isValue(ei) } match {
        case Some((fi,ei)) =>
          for (eip <- step(ei)) yield Obj(fields + (fi -> eip))
        case None => throw StuckError(e)
      }
      //SearchGetField
      case GetField(e1, f) => 
      if(e1 == Null) throw NullDereferenceError(e1)
        for (e1p <- step(e1)) yield GetField(e1p, f)
      
      /*** Fill-in more Search cases here. ***/
      //SearchDecl
      case Decl(mut, x, e1, e2) =>
        for (e1p <- step(e1)) yield Decl(mut, x, e1p, e2)
      //SearchAssign2
      case Assign(e1,e2) if (isLValue(e1) && !isLValue(e2)) => for(e2p <- step(e2)) yield Assign(e1, e2p)
      //SearchAssign1
      case Assign(v1, e2) => for (e1p <- step(v1)) yield Assign(e1p, e2)
      //SearchCall
      case Call(e1, args) => 
        for (e1p <- step(e1)) yield Call(e1p, args)
      
        
      /* Everything else is a stuck error. */
      case _ => throw StuckError(e)
    }
  }

  /*** External Interfaces ***/

  this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(500) // comment this out or set to None to not bound the number of steps.
  
  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  
  case class TerminationError(e: Expr) extends Exception {
    override def toString = Parser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
  }
  
  def iterateStep(e: Expr): Expr = {
    require(closed(e), "not a closed expression: free variables: %s".format(freeVars(e)) )
    def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
      if (Some(n) == maxSteps) throw TerminationError(e)
      else if (isValue(e)) doreturn( e )
      else {
        for {
          m <- doget[Mem]
          _ = if (debug) { println("Step %s:%n  %s%n  %s".format(n, m, e)) }
          ep <- step(e)
          epp <- loop(ep, n + 1)
        } yield
        epp
      }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val (m,v) = loop(e, 0)(Mem.empty)
    if (debug) {
      println("Result:%n  %s%n  %s".format(m,v))
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(removeInterfaceDecl(jsy.lab5.Parser.parse(s)))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab5.Parser.parseFile(file)
      }} getOrElse {
        return
      }
      
    val exprlowered =
      handle(None: Option[Expr]) {Some{
        removeInterfaceDecl(expr)
      }} getOrElse {
        return
      }  
    
    handle() {
      val t = inferType(exprlowered)
    }
    
    handle() {
      val v1 = iterateStep(exprlowered)
      println(pretty(v1))
    }
  }
    
}