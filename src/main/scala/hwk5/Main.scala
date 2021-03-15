
package hwk5;

import java.io.File
import common.GenerateAST
 

object Main {
  def main(args: Array[String]) { 
    val ast = GenerateAST(new File("test/uv1.js")) 
	  
    ast.prep 
    ast.buildGraph(Map())
     
//    val a = UV(ast)
    val a = CSUV(ast)
    
    a.worklist
    println(a) 
    println
    print(a.toDotGraph)
  }
}
