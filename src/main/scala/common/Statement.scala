package common
 
sealed abstract class Statement extends AbstractSyntaxTree {
  // add label to statements and add height
  def prep {
    this.setid
    this match {
    case Script(stmts) => { addHeights(stmts); stmts.foreach(s => s.prep) }
    case BlockStmt(stmts) => { addHeights(stmts); stmts.foreach(s => s.prep) }
    case VarDeclListStmt(decls) => { addHeights(decls); decls.foreach(s => s.prep) }
    case FunctionDecl(_, fun) => { fun.height = height; val body = fun.asInstanceOf[FunctionExpr].body; addHeight(body); body.prep }
    case IfStmt(_, thenPart, elsePart) => { addHeights(List(thenPart, elsePart)); thenPart.prep; elsePart.prep } 
    case SwitchStmt(_, cases, defaultCase) => { 
      val d =  cases ++ (defaultCase match {case Some(c) => {c.default=true; List(c)} case None => List()})
      addHeights(d)
      d.foreach(c => c.prep)
    }
    case CaseStmt(_, body) => { addHeight(body); body.prep }
    case DoWhileStmt(_, body) => { addHeight(body); body.prep }
    case WhileStmt(_, body) => { addHeight(body); body.prep }
    case ForStmt(_, _, _, body) => {  addHeight(body); body.prep }
    case ForInStmt(_, _, body) => { addHeight(body); body.prep }
    case LabeledStmt(_, body) => { addHeight(body); body.prep }
    case _ => 
    }
  }
  
  override def toString = this match {
    case Script(stmts) => toString(stmts)
    case BlockStmt(stmts) => space + "{\n" + toString(stmts) + space + "}"
    case VarDeclListStmt(decls) => toString(decls)
    case EmptyStmt() => ""
    case ExprStmt(expr) => space + expr.toString
    case VarDeclStmt(name, expr) => { 
      val e = expr match { case EmptyExpr() => "" case _ => " = " + expr }
      space + "var " + name + e
    }
    case FunctionDecl(name, fun) =>  fun.toString
    case ReturnStmt(expr) => space + "return " + expr
    case IfStmt(cond, thenPart, elsePart) => { 
      val e = elsePart match { case EmptyStmt() => "" case _ => " else\n" + elsePart }
      space + "if (" + cond + ") " + "\n" + thenPart + e
    }
    case SwitchStmt(cond, cases, defaultCase) => {      
      val d =  cases ++ (defaultCase match {case Some(c) => List(c) case None => List()}) 
      space + "switch (" + cond + ") {\n" + d.foldRight("")((s, c) => s + "\n" + c) + space + "}"
    }
    case c@CaseStmt(expr, body) => { 
      c.default match {
        case true => space + "default :\n" + body
        case false => space + "case " + expr + " :\n" + body
      }
    }
    case BreakStmt(breakLabel) => space + "break " + breakLabel
    case ContinueStmt(continueLabel) => space + "continue " + continueLabel
    case DoWhileStmt(cond, body) => space + "do\n" + body + "while (" + cond + ")\n" 
    case WhileStmt(cond, body) =>  space + "while (" + cond + ")\n" + body  
    case ForStmt(init, cond, increment, body) => { 
      val c = cond match { case Some(x)=>x.toString case None => "" }
      val i = increment match { case Some(x)=>x.toString case None => "" }
      space + "for (" + init + "; " + c + "; " + i + ")\n" + body
    }
    case ForInStmt(init, expr, body) => space + "for (" + init + " in " + expr + ")" + body
    case LabeledStmt(label, body) => label.foldRight("")((e,c) => space + e + ":\n" + c) + body 
    case _ => ""
  }
  
  def toString(stmts: List[Statement]) = stmts.foldRight("")((s, c) =>  
    (s match { 
      case WhileStmt(_,_) => s+"\n"
      case DoWhileStmt(_,_) => s+"\n"
      case ForStmt(_,_,_,_) => s+"\n"
      case ForInStmt(_,_,_) => s+"\n"
      case FunctionDecl(_,_) => s+"\n"
      case IfStmt(_,_,_) => s+"\n"
      case SwitchStmt(_,_,_) => s+"\n" 
      case EmptyStmt() => ""
      case _ =>  s + ";\n"  
    }) + c
  )
  
  private def separate_functions(stmts: List[Statement]) = 
    stmts.foldRight((List[FunctionDecl](), List[Statement]())) (
        (e, c) => e match { case f@FunctionDecl(_,_) => (f::c._1, c._2) case _ => (c._1, e::c._2) }
    )
  
  def entry: Statement = this match {
    case Script(stmts) => {
      val (_, main) = separate_functions(stmts) 
      main.head.entry       // assume script or block is not empty
    }
    case BlockStmt(stmts) => {
      val (_, main) = separate_functions(stmts) 
      main.head.entry       // assume script or block is not empty
    }
    case VarDeclListStmt(decls) => decls.head.entry
    case DoWhileStmt(_, body) => body.entry 
    case LabeledStmt(_, stmt) => stmt.entry
    case FunctionDecl(_, exp) => exp.asInstanceOf[FunctionExpr].body.entry
    case _ => this
  }
  
  def exit: List[Statement] = this match {
    case Script(stmts) => stmts.last.exit       // assume script or block is not empty
    case BlockStmt(stmts) => stmts.last.exit
    case VarDeclListStmt(decls) => decls.last.exit 
    case IfStmt(_, thenPart, elsePart) => thenPart.exit ::: (elsePart match { case EmptyStmt() => List(this) case _ => elsePart.exit })
    case SwitchStmt(_, cases, defaultCase) => {
       val d = defaultCase match {case None => cases case Some(x) => cases++List(x)}
       d.last.exit
    }
    case CaseStmt(_,body) => body.exit 
    case LabeledStmt(_, stmt) => stmt.exit
    case _ => List(this)
  }
  
  var succ : List[Statement] = List()
  var pred : List[Statement] = List()
  var call : Option[FunctionDecl] = None // only make sense for statement with function call  
  
  def addSucc(s: Statement) { succ = s :: succ; s.pred = this :: s.pred }
  
  def buildGraph(stmts: List[Statement], map: Map[String, FunctionDecl]) {
    val (funs, main) = separate_functions(stmts)
        
    val map1 = map ++ funs.map(f => (f.name.str, f)).toMap
    
    stmts.foreach(f => f.buildGraph(map1))
    
    def h (stmts: List[Statement]) {
      stmts match {
        case Nil => 
        case List(s) =>  
        case s1::s2::r => { 
          h(s2::r)
          val ex = s1.exit
          val et = s2.entry
          for(e <- ex) {
            e.addSucc(et)
          }
        }
      } 
    }
    h(main)
  }

  def buildGraph (map: Map[String, FunctionDecl]): Unit = this match {
    case Script(stmts) => buildGraph(stmts, map)  
    case BlockStmt(stmts) => buildGraph(stmts, map)
    case VarDeclListStmt(decls) => buildGraph(decls, map)
    case IfStmt(_, thenPart, elsePart) => {
      thenPart.buildGraph(map)
      this.addSucc(thenPart.entry)
      elsePart match {
        case EmptyStmt() => 
        case _ => { 
          elsePart.buildGraph(map)
          this.addSucc(elsePart.entry)
        }
      }
    }
    case SwitchStmt(_, cases, defaultCase) => {
      val d = defaultCase match {case None => cases case Some(x) => cases++List(x)}
      buildGraph(d, map)
      for(c <- d) {
        addSucc(c.entry) 
      }
    }
    case DoWhileStmt(_, body) => {
      body.buildGraph(map)
      this.addSucc(body.entry)
      for(e <-body.exit) {
        e.addSucc(this)
      }
    }
    case WhileStmt(_, body) => {
      body.buildGraph(map)
      this.addSucc(body.entry)
      for(e <- body.exit) {
        e.addSucc(this)
      }
    }
    // a function declaration has a name and a function expression (information like function name is duplicated)
    case FunctionDecl(name, exp) => {
      val body = exp.body
      body.buildGraph(map) 
    }
    case ExprStmt(FuncCall(VarRef(name), args)) => {
      val fun = map(name)
      this.call = Some(fun) 
    }
    case ExprStmt(AssignExpr(_, _, FuncCall(VarRef(name), args))) => {
      val fun = map(name)
      this.call = Some(fun) 
    }
    case VarDeclStmt(_, FuncCall(VarRef(name), args)) => {
    	val fun = map(name)
      this.call = Some(fun) 
    }
    case _ =>
  }
  
  def dotStr : String = "\"" + this.id + " : " + (this match {
    case Script(stmts) => stmts.head.dotStr
    case BlockStmt(stmts) => stmts.head.dotStr
    case VarDeclListStmt(decls) => decls.head.dotStr 
    case IfStmt(cond, _, _) => cond.toString
    case WhileStmt(cond, _) => cond.toString
    case DoWhileStmt(cond, _) => cond.toString
    case FunctionDecl(name, _) => "function " + name 
    case _ => this.toString.trim 
  }) + "\""
  
  def toDot : List[String] = this match {
    case Script(stmts) => toDot(stmts)
    case BlockStmt(stmts) => toDot(stmts)
    case VarDeclListStmt(decls) => toDot(decls)
    case IfStmt(cond, thenPart, elsePart) => thenPart.toDot ++ elsePart.toDot ++ toDot(this) 
    case WhileStmt(cond, body) => List(toSubgraph(body.toDot, this.id)) ++ toDot(this)
    case DoWhileStmt(cond, body) => List(toSubgraph(body.toDot, this.id)) ++ toDot(this)
    case FunctionDecl(name, expr) => List(toSubgraph(expr.body.toDot, this.id)) ++ toDot(this)
    case _ => toDot(this) 
  }
  
  def toDot(s: Statement) = s.succ.map(e => s.id + " -> " + e.id)
  def toDot (stmts: List[Statement]) : List[String] = stmts.flatMap(s => s.toDot)  
  
  def toSubgraph (edges: List[String], id: Long) = "subgraph cluster_" + id + 
                                         " {\n" + (edges.reduceLeft((c,e) => c + "\n" + e)) + "\n}" 
}

case class Script(stmts : List[Statement]) extends  Statement
case class BlockStmt(stmts : List[Statement]) extends Statement
case class VarDeclListStmt(decls : List[Statement]) extends Statement
case class EmptyStmt() extends Statement
case class ExprStmt(expr : Expression) extends Statement()
case class VarDeclStmt(name : IntroduceVar, expr : Expression) extends Statement
case class FunctionDecl(name : IntroduceVar, fun : FunctionExpr) extends Statement
case class ReturnStmt(expr : Expression) extends Statement
case class IfStmt(cond : Expression, thenPart : Statement, elsePart : Statement) extends Statement
case class SwitchStmt(cond : Expression, cases : List[CaseStmt], defaultCase : Option[CaseStmt]) extends Statement
case class CaseStmt(expr : Expression, body : Statement) extends Statement { var default = false }
case class BreakStmt(breakLabel : String) extends Statement
case class ContinueStmt(continueLabel : String) extends Statement
case class DoWhileStmt(cond : Expression, body : Statement) extends Statement
case class WhileStmt(cond : Expression, body : Statement) extends Statement
case class ForStmt(init : ForInit, cond : Option[Expression], increment : Option[Expression], body : Statement) extends Statement
case class ForInStmt(init : ForInInit, expr : Expression, body : Statement) extends Statement
case class LabeledStmt(label : List[String], stmt : Statement) extends Statement
case class TryStmt(body : Statement, catchClause : List[CatchStmt], finalCatch : Option[Statement]) extends Statement
case class CatchStmt(name : IntroduceVar, body : Statement) extends Statement
case class ThrowStmt(expr : Expression) extends Statement
