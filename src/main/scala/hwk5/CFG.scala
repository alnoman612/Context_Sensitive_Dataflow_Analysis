package hwk5

import common._
import scala.collection.mutable.Set
import scala.collection.mutable.Map

trait CFG {
  val stmt: Statement // program to be analyzed
  val extremal : Node  // node with extremal label
    
  // retrieve the successors and predecessors of a CFG node
  def succ(n: Node) : Set[Node]
  def pred(n: Node) : Set[Node]
  
  def bypass(n: Node) : Set[Node] // returns the RetNode of a CallNode (forward) or the callNode of a RetNode (backward)
  
  // artificial entry/exit nodes of the main program 
	val (entry, exit) = (EntryNode(None), ExitNode(None)) 
	
  val cmap = Map[Statement, (CallNode, RetNode)]()          // call/return nodes of call sites
  private val imap = Map[Statement, IntraNode]()                    // intra-procedural CFG nodes
  val fmap = Map[FunctionDecl, (EntryNode, ExitNode, Set[Node])]()     // entry/exit/all nodes of functions 
  
  private def getEntry(s: Statement) = if (imap.contains(s)) imap(s) else cmap(s)._1
  private def getExit(s: Statement) = if (imap.contains(s)) imap(s) else cmap(s)._2
  
  // collect the CFG statements from a program
	private def cfgNodes = {
    def h (stmt: Statement, nodes: Set[Node]) { 
      stmt.call match {
        case None => if (!imap.contains(stmt)) {
          val n = IntraNode(stmt)
          nodes += n
        	imap += stmt -> n
        	for(s <- stmt.succ) {
        	  h(s, nodes)
        	  n.addSucc(getEntry(s))
        	}
        }
        case Some(decl) => if (! cmap.contains(stmt)) {
          if (!fmap.contains(decl)) {
            val (n1, n2) = (EntryNode(Some(decl)), ExitNode(Some(decl)))
            val b = decl.fun.body  
            val nodes1 = Set[Node](n1, n2)
            fmap += ((decl, (n1, n2, nodes1))) 
            h(b.entry, nodes1) 
            n1.addSucc(getEntry(b.entry)) 
            for(e <- b.exit) getExit(e).addSucc(n2)
          }     
          val (entry, exit, _) = fmap(decl)
          val (call, ret) = (CallNode(stmt, entry), RetNode(stmt, exit))
          call.addSucc(ret)
          nodes += call += ret
     		  cmap += stmt -> (call, ret)
     		  entry.calls += call
     		  exit.rets += ret
     		  for(s <- stmt.succ) {
     		    h(s, nodes)
     		    ret.addSucc(getEntry(s))
     		  }
        }
      }
    } 			 
	  h(stmt.entry, main_nodes) 
    entry.addSucc(getEntry(stmt.entry)) 
    for(e <- stmt.exit) getExit(e).addSucc(exit) 
	}
 
  private val main_nodes = Set[Node](entry, exit)
  cfgNodes 
  
  val nodes = main_nodes ++ fmap.values.map(x=>x._3).foldLeft(Set[Node]())((c, e) => c ++ e)
  
  def toDotGraph = {
		val indices = nodes.zipWithIndex.toMap
		  
    def h(i: Int, entry: Node, exit: Node, nodes: Set[Node]) = 
      s"subgraph cluster_$i {\n{rank=source ${indices(entry)}} {rank=sink ${indices(exit)}}\n${nodes.flatMap(n=>n.succ.map(s=>indices(n)+" -> "+indices(s))).mkString("\n")}\n}"

    val edges = (fmap.values ++ List((entry, exit, main_nodes))).zipWithIndex.map(x => {
      val ((entry, exit, nodes), i) = x
      h (i, entry, exit, nodes)
    })
    val inter = for{
        (c,r) <- cmap.values 
        s <- List(indices(c) + " -> " + indices(c.to), indices(r.from) + " -> " + indices(r))
    } yield (s+"[style=dashed, color=grey]")
    
    edges ++ inter
  }
  
  def call_ret (node: CallNode) = cmap(node.stmt)._2
  def call_ret (node: RetNode) = cmap(node.stmt)._1
}

trait Node { 
  val succ = Set[Node]()
  val pred = Set[Node]()
  def addSucc(n: Node) {
    succ += n
    n.pred += this
  }
  def dotStr = this match {
    case IntraNode(stmt) => stmt.dotStr
    case CallNode(stmt, to) => stmt.dotStr
    case RetNode(stmt, from) => stmt.dotStr
    case EntryNode(f) => "\"enter " + (f match {case None => "main\"" case Some(d) => d.name.str+"\""})
    case ExitNode(f) => "\"exit " + (f match {case None => "main\"" case Some(d) => d.name.str+"\""})
  }
}

case class IntraNode(stmt: Statement) extends Node
case class CallNode (stmt: Statement, to: EntryNode)   extends Node 
case class RetNode  (stmt: Statement, from: ExitNode)  extends Node
case class EntryNode(f: Option[FunctionDecl]) extends Node { val calls = Set[Node]() }
case class ExitNode (f: Option[FunctionDecl]) extends Node { val rets  = Set[Node]() }

case class ForwardCFG(stmt: Statement) extends CFG { 
  val extremal = entry 

	def succ(node: Node) = node match {
    case CallNode(_, to) => Set(to)
    case n@ExitNode(_) => n.rets
    case _ => node.succ
  }
  def pred(node: Node) = node match {
    case RetNode(_, from) => Set(from) 
    case n@EntryNode(_) => n.calls
    case _ => node.pred
  }
  def bypass(node: Node) = node match {
    case CallNode(_,_) => node.succ
    case _ => Set()
  }
}

case class BackwardCFG(stmt: Statement) extends CFG {
  val extremal = exit
  
  def succ(node: Node) = node match {
    case RetNode(_, from) => Set(from)  
    case n@EntryNode(_) => n.calls
    case _ => node.pred
  }
  def pred(node: Node) = node match {
    case CallNode(_, to) => Set(to)
    case n@ExitNode(_) => n.rets
    case _ => node.succ
  }
  def bypass(node: Node) = node match {
    case RetNode(_,_) => node.pred
    case _ => Set()
  }
}
