package common;

import AssignOp.AssignOp
import InfixOp.InfixOp
import PrefixOp.PrefixOp
import UnaryAssignOp.UnaryAssignOp  
 
sealed abstract class Expression extends AbstractSyntaxTree {
  override def toString = this match {
    case EmptyExpr() => ""
    case FunctionExpr(name, ps, body) => { 
      val n = name match {case Some(x) => x; case None => ""}
      space + "function " + n + "(" + toString(ps) + ")\n" +  body
    }
    case VarRef(name) => name
    case ThisRef() => "this"
    case DotRef(obj, prop) => obj + "." + prop
    case BracketRef(obj, prop) => obj + "[" + prop + "]"
    case MethodCall(receiver, method, args) => receiver + 
                                              (method match { case StringLit(x) => "." + x case _ => "[" + method + "]" }) + 
                                              "(" + toString(args) + ")"
    case FuncCall(func, args) => func + "(" + toString(args) + ")"
    case NewCall(constructor, args) => "new " + constructor + "(" + toString(args) + ")"
    case AssignExpr(op, lv, expr) => lv + " " + op + " " + expr
    case NullLit() => "null"
    case BoolLit(value) => value.toString
    case NumberLit(value) => value.toString
    case StringLit(value) => "\'"+value+"\'"
    case RegExp(regexp, _,_) => regexp.toString
    case ObjectLit(obj) => "{" + toString(obj) + "}"
    case ArrayLit(vs) => "[" + toString(vs) + "]"
    case UnaryAssignExpr(op, lv) => op.toString + " " + lv
    case PrefixExpr(op, exp) => op.toString + " " + exp
    case InfixExpr(op, exp1, exp2) => exp1 + " " + op + " " + exp2
    case CondExpr(cond, thenPart, elsePart) => cond + " ? " + thenPart + " : " + elsePart
    case ListExpr(exprs) => "(" + toString(exprs) + ")"
  }
  
  def toString[A](lst: List[A]) = 
    lst match {
    case Nil => ""
    case x::r => r.foldLeft(x.toString)((c, p) => c + ", " + p)
  }
}

case class EmptyExpr() extends Expression
case class FunctionExpr(name : Option[IntroduceVar], ps : List[IntroduceVar], body : Statement) extends Expression { 
  var freeVariables = Set.empty[String]
}
case class VarRef(name : String) extends Expression with VariableAccess
case class ThisRef() extends Expression
case class DotRef(obj : Expression, prop : String) extends Expression
case class BracketRef(obj : Expression, prop : Expression) extends Expression
case class MethodCall(receiver : Expression, method : Expression, args : List[Expression]) extends Expression
case class FuncCall(func : Expression, args : List[Expression]) extends Expression
case class NewCall(constructor : Expression, args : List[Expression]) extends Expression 
case class AssignExpr(op : AssignOp, lv : LValue, expr : Expression) extends Expression
case class NullLit() extends Expression
case class BoolLit(value : Boolean) extends Expression
case class NumberLit(value : Double) extends Expression
case class StringLit(value : String) extends Expression
case class RegExp(regexp : String, global : Boolean, case_insensitive : Boolean) extends Expression 
case class ObjectLit(obj : List[ObjectPair]) extends Expression
case class ArrayLit(vs : List[Expression]) extends Expression
case class UnaryAssignExpr(op : UnaryAssignOp, lv: LValue) extends Expression
case class PrefixExpr(op : PrefixOp, expr : Expression) extends Expression
case class InfixExpr(op : InfixOp, expr1 : Expression, expr2 : Expression) extends Expression
case class CondExpr(cond : Expression, thenPart : Expression, elsePart : Expression) extends Expression
case class ListExpr(exprs : List[Expression]) extends Expression


object AssignOp extends Enumeration {
  type AssignOp = Value
  val OpAssign=Value("=");         val OpAssignAdd=Value("+="); 
  val OpAssignSub=Value("-=");     val OpAssignMul=Value("*="); 
  val OpAssignDiv=Value("/=");     val OpAssignMod=Value("%="); 
  val OpAssignLShift=Value("<<="); val OpAssignSpRShift=Value(">>="); val OpAssignZfRShift=Value(">>>="); 
  val OpAssignBAnd=Value("&=");    val OpAssignBXor=Value("^=");      val OpAssignBOr=Value("|=");
}

object UnaryAssignOp extends Enumeration {
  type UnaryAssignOp = Value
  val PrefixInc=Value("++"); val PrefixDec=Value("--"); val PostfixInc=Value("++"); val PostfixDec = Value("--")
}

object PrefixOp extends Enumeration {
  type PrefixOp = Value
  val PrefixLNot=Value("!");        val PrefixBNot=Value("~"); 
  val PrefixPlus=Value("+");        val PrefixMinus=Value("-"); 
  val PrefixTypeof=Value("typeof"); val PrefixVoid=Value("void"); val PrefixDelete = Value("delete")
}

object InfixOp extends Enumeration {
  type InfixOp = Value
  val OpLT=Value("<");      val OpLEq=Value("<=");       val OpGT=Value(">");         val OpGEq=Value(">="); 
  val OpEq=Value("==");     val OpNEq=Value("!=");       val OpStrictEq=Value("==="); val OpStrictNEq=Value("!==");
  val OpIn=Value("in");     val OpInstanceof=Value("instanceof"); 
  val OpLAnd=Value("&&");   val OpLOr=Value("||"); 
  val OpMul=Value("*");     val OpDiv=Value("/");        val OpMod=Value("%");        val OpSub=Value("-"); val OpAdd=Value("+")
  val OpLShift=Value("<<"); val OpSpRShift=Value(">>");  val OpZfRShift=Value(">>>"); 
  val OpBAnd=Value("&");    val OpBXor=Value("^");       val OpBOr=Value("|"); 
}