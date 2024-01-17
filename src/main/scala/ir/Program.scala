package ir

import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable
import boogie.*
import analysis.BitVectorEval

class Program(var procedures: ArrayBuffer[Procedure], var mainProcedure: Procedure, var initialMemory: ArrayBuffer[MemorySection], var readOnlyMemory: ArrayBuffer[MemorySection]) {

  // This shouldn't be run before indirect calls are resolved


  def stripUnreachableFunctions(depth: Int = Int.MaxValue): Unit = {
    val procedureCalleeNames = procedures.map(f => f.name -> f.calls.map(_.name)).toMap

    var toVisit: mutable.LinkedHashSet[(Int, String)] = mutable.LinkedHashSet((0, mainProcedure.name))
    var reachableFound = true
    val reachableNames = mutable.HashMap[String, Int]()
    while (toVisit.nonEmpty) {
      val next = toVisit.head
      toVisit.remove(next)

      if (next._1 <= depth) {

        def addName(depth: Int, name: String): Unit = {
          val oldDepth = reachableNames.getOrElse(name, Integer.MAX_VALUE)
          reachableNames.put(next._2, if depth < oldDepth then depth else oldDepth)
        }
        addName(next._1, next._2)

        val callees = procedureCalleeNames(next._2)

        toVisit.addAll(callees.diff(reachableNames.keySet).map(c => (next._1 + 1, c)))
        callees.foreach(c => addName(next._1 + 1, c))
      }
    }
    procedures = procedures.filter(f => reachableNames.keySet.contains(f.name))

    for (elem <- procedures.filter(c => c.calls.exists(s => !procedures.contains(s)))) {
      // last layer is analysed only as specifications so we remove the body for anything that calls
      // a function we have removed
      elem.blocks.clear()
    }
  }

  def setModifies(specModifies: Map[String, List[String]]): Unit = {
    val procToCalls: mutable.Map[Procedure, Set[Procedure]] = mutable.Map()
    for (p <- procedures) {
      p.modifies.addAll(p.blocks.flatMap(_.modifies))
      procToCalls(p) = p.calls
    }

    for (p <- procedures) {
      if (specModifies.contains(p.name)) {
        p.modifies.addAll(specModifies(p.name).map(nameToGlobal))
      }
    }

    // very naive implementation but will work for now
    var hasChanged: Boolean = true
    while (hasChanged) {
      hasChanged = false
      for (p <- procedures) {
        val children = procToCalls(p)
        val childrenModifies: mutable.Set[Global] = mutable.Set()
        for (c <- children) {
          childrenModifies.addAll(c.modifies)
        }
        if (!childrenModifies.subsetOf(p.modifies)) {
          hasChanged = true
          p.modifies.addAll(childrenModifies)
        }
      }
    }
  }

  // this is very crude but the simplest thing for now until we have a more sophisticated specification system that can relate to the IR instead of the Boogie
  def nameToGlobal(name: String): Global = {
    if ((name.startsWith("R") || name.startsWith("V")) && (name.length == 2 || name.length == 3) && name.substring(1).forall(_.isDigit)) {
      if (name.startsWith("R")) {
        Register(name, BitVecType(64))
      } else {
        Register(name, BitVecType(128))
      }
    } else {
      Memory(name, 64, 8)
    }
  }

  /**
    * Takes all the memory sections we get from the ADT (previously in initialMemory) and restricts initialMemory to
    * just the .data section (which contains things such as global variables which are mutable) and puts the .rodata
    * section in readOnlyMemory. It also takes the .rela.dyn entries taken from the readelf output and adds them to the
    * .rodata section, as they are the global offset table entries that we can assume are constant.
    */
  def determineRelevantMemory(rela_dyn: Map[BigInt, BigInt]): Unit = {
    val initialMemoryNew = ArrayBuffer[MemorySection]()

    val rodata = initialMemory.collect { case s if s.name == ".rodata" => s }
    readOnlyMemory.addAll(rodata)

    val data = initialMemory.collect { case s if s.name == ".data" => s }
    initialMemoryNew.addAll(data)

    // assuming little endian, adding the rela_dyn offset/address pairs like this is crude but is simplest for now
    for ((offset, address) <- rela_dyn) {
      val addressBV = BitVecLiteral(address, 64)
      val bytes = for (i <- 0 to 7) yield {
        val low = i * 8
        val high = low + 8
        BitVectorEval.boogie_extract(high, low, addressBV)
      }
      readOnlyMemory.append(MemorySection(s".got_$offset", offset.intValue, 8, bytes))
    }

    initialMemory = initialMemoryNew
  }


}

class Procedure(
    var name: String,
    var address: Option[Int],
    var blocks: ArrayBuffer[Block],
    var in: ArrayBuffer[Parameter],
    var out: ArrayBuffer[Parameter]
) {
  def calls: Set[Procedure] = blocks.flatMap(_.calls).toSet
  override def toString: String = {
    s"Procedure $name at ${address.getOrElse("None")} with ${blocks.size} blocks and ${in.size} in and ${out.size} out parameters"
  }
  var modifies: mutable.Set[Global] = mutable.Set()

}

class Block(
    var label: String,
    var address: Option[Int],
    var statements: ArrayBuffer[Statement],
    var jump: Jump
) {
  def calls: Set[Procedure] = jump.calls
  def modifies: Set[Global] = statements.flatMap(_.modifies).toSet
  //def locals: Set[Variable] = statements.flatMap(_.locals).toSet ++ jumps.flatMap(_.locals).toSet

  override def toString: String = {
    // display all statements and jumps
    val statementsString = statements.map(_.toString).mkString("\n")
    s"Block $label with $statementsString\n$jump"
  }

  override def equals(obj: scala.Any): Boolean =
    obj match
      case b: Block => b.label == this.label
      case _        => false

  override def hashCode(): Int = label.hashCode()
}

class Parameter(var name: String, var size: Int, var value: Register) {
  def toBoogie: BVariable = BParam(name, BitVecBType(size))
  def toGamma: BVariable = BParam(s"Gamma_$name", BoolBType)
}

/**
  * @param name name
  * @param address initial offset of memory section
  * @param size number of bytes
  * @param bytes sequence of bytes represented by BitVecLiterals of size 8
  */
case class MemorySection(name: String, address: Int, size: Int, bytes: Seq[BitVecLiteral])
