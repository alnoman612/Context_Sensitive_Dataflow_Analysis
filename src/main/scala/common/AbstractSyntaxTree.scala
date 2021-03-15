package common
 
trait AbstractSyntaxTree {
  var height = 0
  
  def addHeight(ast: AbstractSyntaxTree) = { ast.height = height + 1 }
  def addHeights(asts: List[AbstractSyntaxTree]) = asts.foreach(addHeight(_))
  def space = " " * height
  
  type Label = Long
  var id : Label = -1
  def setid { id = AbstractSyntaxTree.freshID }
}

object AbstractSyntaxTree {
  type Label = Long
  var idSeed: Label = 0
  def freshID = {
    idSeed += 1
    idSeed
  }
}

// auxiliary definition for variable use/def
trait VariableAccess { var referTo : IntroduceVar = null } 
case class IntroduceVar(str : String) extends AbstractSyntaxTree { override def toString = str }
 
// auxiliary definition for for-in-loop
sealed abstract class ForInInit extends AbstractSyntaxTree {
  override def toString = this match {
    case ForInVarDecl(name) => "var " + name.toString
    case ForInLValue(lVal) => lVal.toString
  }
}

case class ForInVarDecl(name : IntroduceVar) extends ForInInit()
case class ForInLValue(lVal : LValue) extends ForInInit()

// auxiliary definition for for-loops
sealed abstract class ForInit extends AbstractSyntaxTree {
  override def toString = this match {
    case NoneInit() => ""
    case VarListInit(vars) => vars.decls match { 
      case Nil => "" 
      case (a::b) => b.foldLeft(a.toString)((c, e) => { val v = e.asInstanceOf[VarDeclStmt]; c + ", " + v.name + " = " + v.expr }) 
    }
    case VarInit(varDecl) => "var " + varDecl.name + (varDecl.expr match { case EmptyExpr() => "" case _ => " = " + varDecl.expr })
    case ExprInit(expr) => expr.toString
  }
}

case class NoneInit() extends ForInit
case class VarListInit(vars: VarDeclListStmt) extends ForInit
case class VarInit(varDecl: VarDeclStmt) extends ForInit
case class ExprInit(expr: Expression) extends ForInit

// auxiliary definition for method calls and assignments
sealed abstract class LValue extends AbstractSyntaxTree {
  override def toString = this match {
    case LVarRef(name) => name
    case LDot(obj, field) => obj + "." + field
    case LBracket(obj, computeField) => obj + "[" + computeField + "]"
  }
}

case class LVarRef(name : String) extends LValue with VariableAccess
case class LDot(obj : Expression, field : String) extends LValue
case class LBracket(obj : Expression, computeField : Expression) extends LValue

// auxiliary definitions for objects
abstract class Property extends AbstractSyntaxTree {
  override def toString = this match {
    case PropVar(name) => name
    case PropString(name) => "\"" + name + "\""
    case PropNum(index) => index.toString
  }
}

case class PropVar(name : String) extends Property
case class PropString(name : String) extends Property
case class PropNum(index : Double) extends Property

case class ObjectPair(property: Property, expr : Expression) extends AbstractSyntaxTree {
  override def toString = property + " : " + expr
}
