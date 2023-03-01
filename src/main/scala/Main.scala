// package scala

import bap._
import boogie._
import translating._
import util.RunUtils

import scala.collection.mutable.{ArrayBuffer, Set}
import scala.collection.{immutable, mutable}
import scala.language.postfixOps
import scala.sys.process._

@main def main(fileName: String, elfFileName: String, options: String*): Unit = {
  val specFileName: Option[String] = if (options.nonEmpty && options.head.endsWith(".spec")) {
    Some(options.head)
  } else {
    None
  }
  val outFileName = if (specFileName.isEmpty) {
    if (options.isEmpty) {
      "boogie_out.bpl"
    } else {
      options.head
    }
  } else {
    if (options.tail.isEmpty) {
      "boogie_out.bpl"
    } else {
      options.tail.head
    }
  }
  val performAnalysis = if options.nonEmpty && options.contains("-analyse") then true else false
  val program: BProgram = RunUtils.generateVCsAdt(fileName, elfFileName, specFileName, performAnalysis)
  RunUtils.writeToFile(program, outFileName)

  // println("boogie boogie_out.bpl" #| "grep --color=always '.*Error.*\\|$'" #| Process(Seq("grep", "--color=always", ".*errors.*\\|$"), None, "GREP_COLORS" -> "'1;33"))
  // ("boogie boogie_out.bpl" #| "grep --color=always '.*Error.*\\|$'" #| Process(Seq("GREP_COLORS='1;32'", "grep", "--color=always", ".*errors.*\\|$"), None, "GREP_COLORS" -> "'1;32")) !
  // "boogie boogie_out.bpl" #| "grep --color=always '.*Error.*\\|$'" #| Process("grep --color=always '.*errors.*\\|$'", None, "GREP_COLORS" -> "'1;33")  !
  //"boogie boogie_out.bpl" #| "grep --color=always '.*Error.*\\|$'" #| "grep --color=always '.*parse errors.*\\|$'" !
}
