//package hwk5
//
//import common.Statement

package hwk5

import common._

// set of variables that may be uninitialized
case class Context(call_strings: List[Long]) {
  val k = 2

  def extend(label: Long) = {
    val x = call_strings ++ List(label)
    Context(if (x.length > k) x.drop(1) else x)
  }
}

case class CSVars(vars: Set[(Context, String)]) extends Lattice[CSVars] {
  def lub(that: CSVars) = CSVars(vars.union(that.vars))

  val contexts = vars.map(x => x._1).toSet

  def variables(ctx: Context) = vars.filter(x => x._1 == ctx).map(x => x._2)

  def inInitialized(e: Expression, ctx: Context) = Util.fv(e).intersect(variables(ctx)).isEmpty

  def kill_gen(y: String, e: Expression) = {
    val gen = for (ctx <- contexts; if inInitialized(e, ctx)) yield (ctx, y)
    val kill = for (ctx <- contexts; if !inInitialized(e, ctx)) yield (ctx, y)
    CSVars(vars -- kill ++ gen)
  }

  def gen(y: String) = CSVars(vars ++ contexts.map(ctx => (ctx, y)))

  def gen(ys: List[String]) = CSVars(vars ++ contexts.flatMap(ctx => ys.map(y => (ctx, y))))

  def extend(lc: Long) = CSVars(contexts.map(ctx => ctx.extend(lc)).toSet.map((ctx: Context) => (ctx, Util.zero)))

  override def toString: String = "{" + vars.toList.sortBy(x => x._2).mkString(",") + "}"
}

case class CSUV(stmt: Statement) extends Analysis[CSVars] {
  val cfg = ForwardCFG(stmt)
  val entry = real_entry
  val exit = real_exit

  val extremalValue = CSVars((Util.vars(stmt) + Util.zero).map(x => (Context(Nil), x)))
  val bottom = CSVars(Set())

  def transfer(node: Node, l: CSVars): CSVars = node match {
    case IntraNode(stmt) => transfer(stmt, l)

    case CallNode(stmt, to) => {
      def h(args: List[Expression]): CSVars = {
        val Some(FunctionDecl(_, FunctionExpr(_, ps, _))) = to.f
        val params = ps.map(p => p.str)
        val l1 = l.extend(stmt.id).gen(params)
        val ye = params zip args
        val gen = for (ctx <- l.contexts; (y, e) <- ye; if l.inInitialized(e, ctx)) yield (ctx.extend(stmt.id), y)
        val kill = for (ctx <- l.contexts; (y, e) <- ye; if l.inInitialized(e, ctx)) yield (ctx.extend(stmt.id), y)
        CSVars(l1.vars -- kill ++ gen)
      }
      stmt match {
        case ExprStmt(FuncCall(_, args)) => h(args)
        case ExprStmt(AssignExpr(_, _, FuncCall(_, args))) => h(args)
        case VarDeclStmt(_, FuncCall(_, args)) => h(args)
        case _ => bottom
      }
    }

    case EntryNode(Some(FunctionDecl(_, FunctionExpr(_,ps,stmt)))) => {
      l.gen((Util.vars(stmt ) -- ps.map(p=> p.str) + Util.ret).toList)
    }
    case ExitNode(Some(_)) => CSVars(l.vars.filter(x=> x._2 == Util.ret))

    case n@RetNode(stmt, _) => {
      val lc = entry(cfg.call_ret(n))

      def h(x: String) = {
        val kill = for (ctx <- lc.contexts; if !l.vars.contains(ctx.extend(stmt.id), Util.ret)) yield (ctx, x)
        val gen = for (ctx <- lc.contexts; if l.vars.contains(ctx.extend(stmt.id), Util.ret)) yield (ctx, x)
      }

      stmt match {
//        case ExprStmt(AssignExpr(_, LVarRef(x), FuncCall(_, _))) => h(x)
//        case VarDeclStmt(IntroduceVar(x), FuncCall(_, _)) => h(x)
        case _ => lc // f(e);
      }
    }
    case _ => l
  }

  def initialized(e: Expression, l: CSVars) = Util.fv(e).intersect(l.vars.map(x => x._2)).isEmpty

  def transfer(stmt: Statement, l: CSVars) = {
    stmt match {
      case VarDeclStmt(IntroduceVar(y), e) => {
        e match {
          case EmptyExpr() => l.gen(y)
          case _ => l.kill_gen(y, e)
        }
      }

      case ExprStmt(AssignExpr(_, LVarRef(y), e)) => l.kill_gen(y, e)
      case ReturnStmt(e) => l.kill_gen(Util.ret, e)
    }
  }

}

