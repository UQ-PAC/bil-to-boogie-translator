// package scala

import BilParser._
import analysis._
import astnodes._
import org.antlr.v4.runtime.{CharStreams, CommonTokenStream}
import org.antlr.v4.runtime.tree.ParseTreeWalker
import translating._
import util.RunUtils
//import vcgen._

import scala.collection.mutable.{ArrayBuffer, Set}
import scala.collection.{immutable, mutable}
import scala.language.postfixOps
import scala.sys.process.*

@main def main(fileName: String, elfFileName: String): Unit = {
  val program: Program = RunUtils.generateVCsAdt(fileName, elfFileName)
  RunUtils.writeToFile(program)

  // println("boogie boogie_out.bpl" #| "grep --color=always '.*Error.*\\|$'" #| Process(Seq("grep", "--color=always", ".*errors.*\\|$"), None, "GREP_COLORS" -> "'1;33"))
  // ("boogie boogie_out.bpl" #| "grep --color=always '.*Error.*\\|$'" #| Process(Seq("GREP_COLORS='1;32'", "grep", "--color=always", ".*errors.*\\|$"), None, "GREP_COLORS" -> "'1;32")) !
  // "boogie boogie_out.bpl" #| "grep --color=always '.*Error.*\\|$'" #| Process("grep --color=always '.*errors.*\\|$'", None, "GREP_COLORS" -> "'1;33")  !
  //"boogie boogie_out.bpl" #| "grep --color=always '.*Error.*\\|$'" #| "grep --color=always '.*parse errors.*\\|$'" !
}
