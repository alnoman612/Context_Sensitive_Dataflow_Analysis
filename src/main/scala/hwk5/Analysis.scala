package hwk5
 
import common._
import scala.collection.mutable.Set
import scala.collection.mutable.Map
import scala.collection.mutable.Queue

// abstract type of the data-flow facts
trait Lattice [L <: Lattice[L]] {
  // meet operator (the least upper bound of 'this' and 'that')
  def lub(that: L): L
}

// Bit Vector framework
trait Analysis[L <: Lattice[L]] {
  val cfg: CFG
  val extremalValue: L
  val bottom: L
  
  // actual entry/exit data-flow facts
  val real_entry = Map[Node, L]()
  val real_exit = Map[Node, L]()
  
  // relative entry/exit data-flow facts
  val entry: Map[Node,L]
  val exit: Map[Node,L]
  
  // transfer function for each statement
  def transfer(node: Node, l: L): L
  
  def worklist {
    val queue = Queue[Node]()
	  queue.enqueue(cfg.nodes.toList:_*) 
	  
	  // initialize entry/exit data-flow facts
	  entry.put(cfg.extremal, extremalValue)  
    for(n <- cfg.nodes.diff(Set(cfg.extremal))) entry.put(n, bottom) 
    for(n <- cfg.nodes) exit.put(n, bottom)

	  while(!queue.isEmpty) {
	    val n = queue.dequeue()
	     
	    // calculate the entry data-flow facts of 'n'
	    val l1 = cfg.pred(n).foldLeft(entry(n))((l, n1) => l.lub(exit(n1)))
	    entry.put(n, l1)
	    // calculate the exit data-flow facts of 'n'
	    val l2 = transfer(n, l1)
	    
	    // if this is different from previous data-flow facts
	    if (l2 != exit(n)) {
	      exit.put(n, l2)
	      for(n1 <- cfg.succ(n)) queue.enqueue((n1 :: cfg.bypass(n1).toList):_*) 
	    } 
	  }
  }
  
  // make a dot graph with actual entry/exit data-flow facts of every node
  def toDotGraph = { 
    val indices = cfg.nodes.zipWithIndex.toMap
    
    val labels = cfg.nodes.toList.map(n=>s"${indices(n)} [label = ${n.dotStr}, xlabel = ${"\""}${real_entry(n)}\\n${real_exit(n)}${"\""}]")
    
    s"digraph {\n${(labels ++ cfg.toDotGraph).reduceLeft((c,e) => c + "\n" + e)}\n}"
  }
  
  override def toString = { 
    cfg.nodes.toList.sortBy(n=>n.dotStr).map(n => f"${n.dotStr}%-25s ${real_entry(n)}%-40s ${real_exit(n)}").mkString("\n")
  }
    
}
