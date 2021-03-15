package common

object Util {
  val ret = "?r"
  val zero = "0"
  
  def aexp(e: Expression): Set[Expression] = 
    e match { 
    case DotRef(o,_) => aexp(o)
    case BracketRef(o,_) => aexp(o)
    case MethodCall(_,_,a) => aexp(a)
    case FuncCall(_,a) => aexp(a)
    case NewCall(_,a) => aexp(a)
    case AssignExpr(_, _, e) => aexp(e) + e // not quite right
    case ObjectLit(obj) => aexp(obj.map(o => o.expr)) 
    case ArrayLit(vs) => aexp(vs) 
    case PrefixExpr(_, e) => aexp(e)
    case InfixExpr(_, e1, e2) => aexp(e1) ++ aexp(e2) + e
    case CondExpr(cond, thenPart, elsePart) => aexp(List(cond,thenPart,elsePart))
    case ListExpr(es) => aexp(es)
    case _ => Set()
  }
  def aexp(es: List[Expression]): Set[Expression] = es.map(e=>aexp(e)).foldLeft(Set[Expression]())(_++_)
  
  def aexp(stmt: Statement): Set[Expression] = {
    stmt match {
      case Script(stmts) => aexps(stmts)
      case BlockStmt(stmts) => aexps(stmts)
      case VarDeclListStmt(stmts) => aexps(stmts)
      case VarDeclStmt(x, e) => aexp(e)
      case ExprStmt(AssignExpr(_, _, e)) => aexp(e) 
      case IfStmt(c, t, e) => aexp(c) ++ aexp(t) ++ aexp(e)
      case WhileStmt(c, b) => aexp(c) ++ aexp(b)
      case DoWhileStmt(c, b) => aexp(c) ++ aexp(b)
      case SwitchStmt(e, cases, d) => aexp(e) ++ aexps(d match { case Some(c) => c::cases case None => cases })
      case CaseStmt(e, s) => aexp(e) ++ aexp(s)
      case _ => Set()
    }
  }
  def aexps(stmts: List[Statement]): Set[Expression] = stmts.map(s => aexp(s)).foldLeft(Set[Expression]())(_++_)
  
  def fv(e: Expression): Set[String] = 
    e match {
    case VarRef(n) => Set(n)
    case DotRef(o,_) => fv(o)
    case BracketRef(o,_) => fv(o)
    case MethodCall(_,m,a) => fv(m) ++ fv(a)
    case FuncCall(_,a) => fv(a)
    case NewCall(_,a) => fv(a)
    case AssignExpr(_, lv, e) => fv(e) // not quite right
    case ObjectLit(obj) => fv(obj.map(o => o.expr)) 
    case ArrayLit(vs) => fv(vs) 
    case PrefixExpr(_, e) => fv(e)
    case InfixExpr(_, e1, e2) => fv(e1) ++ fv(e2)
    case CondExpr(cond, thenPart, elsePart) => fv(List(cond,thenPart,elsePart))
    case ListExpr(es) => fv(es)
    case _ => Set()
  }
  def fv(es: List[Expression]): Set[String] = es.map(e=>fv(e)).foldLeft(Set[String]())(_++_)
  
  def vars(stmt: Statement): Set[String] = {
    stmt match {
      case Script(stmts) => vars(stmts)
      case BlockStmt(stmts) => vars(stmts)
      case VarDeclListStmt(stmts) => vars(stmts)
      case VarDeclStmt(x, e) => Set(x.str) ++ fv(e)
      case ExprStmt(AssignExpr(_, LVarRef(n), e)) => Set(n) ++ fv(e) 
      case IfStmt(b, t, e) => fv(b) ++ vars(t) ++ vars(e)
      case WhileStmt(e, b) => fv(e) ++ vars(b)
      case DoWhileStmt(e, b) => fv(e) ++ vars (b)
      case SwitchStmt(e, cases, d) => fv(e) ++ vars(d match { case Some(c) => c::cases case None => cases }) 
      case CaseStmt(e, s) => fv(e) ++ vars(s)
      case ExprStmt(e) => fv(e)
      case _ => Set()
    }
  }
  def vars(stmts: List[Statement]): Set[String] = stmts.map(s => vars(s)).foldLeft(Set[String]())(_++_)
  
}