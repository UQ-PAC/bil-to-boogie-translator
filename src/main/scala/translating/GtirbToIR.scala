package translating
import com.google.protobuf.ByteString
import scala.collection.mutable
import com.grammatech.gtirb.proto
import com.grammatech.gtirb.proto.CFG.CFG
import com.grammatech.gtirb.proto.IR.IR
import com.grammatech.gtirb.proto.Module.Module
import com.grammatech.gtirb.proto.Section.Section
import Parsers.*
import Parsers.SemanticsParser.*
import gtirb.*
import ir._
import scala.collection.mutable.ArrayBuffer
import scala.jdk.CollectionConverters._
import java.awt.Taskbar.State
import java.util.Base64
import com.grammatech.gtirb.proto.CFG.Edge._
import scala.collection.mutable.HashMap
import java.nio.charset.*
import scala.util.boundary, boundary.break
import java.nio.ByteBuffer
import intrusivelist.{IntrusiveList, IntrusiveListElement}

/**
* TempIf class, used to temporarily store information about Jumps so that multiple parse runs are not needed. 
* Specifically, this is useful in the case that the IF statment has multiple conditions( and elses) and as such many extra blocks 
* need to be created. 
*
* @param isLongIf: if this IF is long(i.e. contains multiple nested if else chains), then true. 
* @param conds: conditions on this if statement 
* @param statements: statements of this if statement 
* @param elsestatement: if this Ifstatement has a self-contained else, it is stored here
*
*/ 
class TempIf(val isLongIf: Boolean, val conds: ArrayBuffer[Expr], val stmts: ArrayBuffer[ArrayBuffer[Statement]], 
              val elseStatement: Option[Statement] = None, override val label: Option[String] = None) extends Assert(conds.head) {}

object TempIf {
  def unapply(tempIf: TempIf): Option[(Boolean, ArrayBuffer[Expr], ArrayBuffer[ArrayBuffer[Statement]], Option[Statement], Option[String])] = {
    Some((tempIf.isLongIf, tempIf.conds, tempIf.stmts, tempIf.elseStatement, tempIf.label))
  }
}

/** 
* GtirbtoIR class. Forms an IR as close as possible to the one produced by BAP by using GTIRB instead 
*
* @param mods: Modules of the Gtirb file. 
* @param parserMap: A Map from UUIDs to basic block statements, used for parsing 
* @param cfg: The cfg provided by gtirb
* @param mainAddress: The address of the main function
*
*/
class GtirbToIR (mods: Seq[com.grammatech.gtirb.proto.Module.Module], parserMap: Map[String, Array[Array[StmtContext]]], cfg: CFG, mainAddress: Int) {

  // Util function used to get Key of a map that maps any K -> Set(V) using V
  def getKey[K, V](value: V, map: mutable.Map[K, mutable.Set[V]]): Option[K] = {
    val v = map.values.find(_.contains(value))
    val key = v.flatMap(v => map.find(_._2 == v).map(_._1))
    return key
  }

  //Creates addresses of blks using gtirb maps
  def create_addresses(): collection.mutable.HashMap[ByteString, Int] = {

    val blockAddresses: HashMap[ByteString, Int] = HashMap.empty

    for {
      mod <- mods
      section <- mod.sections
      byteInterval <- section.byteIntervals
      block <- byteInterval.blocks
      if (!block.getCode.uuid.isEmpty)
    } {
      blockAddresses += (block.getCode.uuid -> (byteInterval.address + block.offset).toInt)
    }

    blockAddresses

  } 

  // Creates CFG map mapping blk UUIDs to a buffer of outgoing edges 
  def create_cfg_map(): (collection.mutable.HashMap[String, ArrayBuffer[proto.CFG.Edge]],collection.mutable.HashMap[String, ArrayBuffer[proto.CFG.Edge]])  = {

    val edges = cfg.edges 
    val edgeMap: HashMap[String, ArrayBuffer[proto.CFG.Edge]] = HashMap.empty
    val incomingEdgeMap: HashMap[String, ArrayBuffer[proto.CFG.Edge]] = HashMap.empty

    for (edge <- edges) { 

      val targetUuid = Base64.getUrlEncoder().encodeToString(edge.targetUuid.toByteArray())
      val sourceUuid = Base64.getUrlEncoder().encodeToString(edge.sourceUuid.toByteArray())

      if (edgeMap.contains(sourceUuid)) {
        edgeMap(sourceUuid) += edge
      } else {
        edgeMap += (sourceUuid -> ArrayBuffer(edge))
      }

      if (incomingEdgeMap.contains(targetUuid)) {
        incomingEdgeMap(targetUuid) += edge
      } else {
        incomingEdgeMap += (targetUuid -> ArrayBuffer(edge))
      }

    }
    (edgeMap, incomingEdgeMap)
  }

  // Another map of blk UUIDs to Symbols related to that blk. 
  // Symbols are usually blk names or strings related to that blk
  def create_symMap(): HashMap[ByteString, mutable.Set[proto.Symbol.Symbol]] = {
    val symMap = HashMap[ByteString, mutable.Set[proto.Symbol.Symbol]]()

    for (sym <- symbols) {
      if (sym.optionalPayload.isReferentUuid) {
        val ruuid = sym.optionalPayload.referentUuid.get

        if (symMap.contains(ruuid)) {
          symMap(ruuid) += sym
        } else {
          symMap += (ruuid -> mutable.Set[proto.Symbol.Symbol](sym))
        }
          
      } 
    }
    symMap
  }

  // Gets name of function using a UUID
  def create_names(uuid: ByteString): String = {
    var name: String = uuid.toString() 

    if (functionNames.get(uuid) != None) { 
      name = symbols.find(functionNames(uuid) == _.uuid).get.name
      

      val entryBlocks: mutable.Set[ByteString] = functionEntries.get(uuid).get

      val result = entryBlocks
        .flatMap(e => edgeMap.getOrElse(Base64.getUrlEncoder().encodeToString(e.toByteArray()), None).iterator) 
        .flatMap(elem => mods.flatMap(_.proxies).find(_.uuid == elem.targetUuid))
        .flatMap(proxy => symMap.getOrElse(proxy.uuid, None))
        .map(p => p.name)

      if (result.nonEmpty) {
        return result.head //. head seems weird here but i guess it works
      }
      
    }

    name
  }

  def get_jmp_reg(statement: Statement): Variable = statement match {
    case LocalAssign(_, rhs: Variable, _) => rhs
    case LocalAssign(_, rhs: Extract, _) => rhs.body.asInstanceOf[Variable]
    case _ => ???
  }

  def get_proc(target: ByteString, procedures: ArrayBuffer[Procedure]): Procedure = {
    val key = getKey(target, functionEntries).get
    procedures.find(_.name == create_names(key)).get
  }

  def create_arguments(name: String): ArrayBuffer[Parameter] = {
    val args = ArrayBuffer.newBuilder[Parameter]
    var regNum = 0 

    if (name == "main") {
      args += Parameter("main_argc", 64, Register("R0", BitVecType(64)))
      args += Parameter("main_argv", 64, Register("R1", BitVecType(64)))
      regNum = 2
    }

    while (regNum < 8) {
      args += Parameter(name + "_arg" + (regNum + 1), 64, Register("R" + regNum, BitVecType(64)))
      regNum += 1
    }

    args.result()
  }


  // Utility Maps used for below functions
  //TODO: mods.head may not work here if multiple modules, in which case decoder needs to change
  val functionNames = MapDecoder.decode_uuid(mods.head.auxData.get("functionNames").get.data)
  val functionEntries = MapDecoder.decode_set(mods.head.auxData.get("functionEntries").get.data)
  val functionBlocks = MapDecoder.decode_set(mods.head.auxData.get("functionBlocks").get.data)
  val symbols = mods.flatMap(_.symbols)
  var blkMap: collection.mutable.HashMap[ByteString, Block] = collection.mutable.HashMap[ByteString, Block]()
  val symMap = create_symMap()
  val addresses = create_addresses()
  val (edgeMap, incomingEdgeMap) = create_cfg_map()
  var blkCount = 0
  var extraBlkCount = 2
 

  def createIR(): Program = {

    var procedures: ArrayBuffer[Procedure] = ArrayBuffer()

    functionEntries.keys.foreach { func =>
      procedures += createProcedure(func)
    }

    procedures = createJumps(procedures)
    val sections = mods.flatMap(_.sections)

    val initialMemory: ArrayBuffer[MemorySection] = sections.map {elem =>
      val bytes = elem.byteIntervals.head.contents.toByteArray.map(byte => BitVecLiteral(BigInt(byte), 8))
      MemorySection(elem.name, elem.byteIntervals.head.address.toInt, elem.byteIntervals.head.size.toInt, bytes.toSeq)
    }.to(ArrayBuffer)

    val readOnlyMemory: ArrayBuffer[MemorySection] = ArrayBuffer() 
    val intialproc: Procedure = procedures.find(_.address.get == mainAddress).get

    return Program(procedures, intialproc, initialMemory, readOnlyMemory)
  }

  def createProcedure(uuid: ByteString): Procedure = {

    val name = create_names(uuid)
    val blocks: ArrayBuffer[Block] = createBlocks(uuid)
    
    
    
    val address: Option[Int] = addresses.get(functionEntries(uuid).head);

    //TODO: function arguments are hardcoded, it's impossible to determine whether a function returns or not. 
      //Function arguments may also be determined through modified liveness analysis but :/
    val in: ArrayBuffer[Parameter] = create_arguments(name)
    val out: ArrayBuffer[Parameter] = ArrayBuffer(Parameter(name + "_result", 64, Register("R0", BitVecType(64)))) 
    return Procedure(name, address, blocks.headOption, None, blocks, in, out)
  }

 

  def createBlocks(uuid: ByteString): ArrayBuffer[Block] = {
    
    val entries = functionEntries(uuid)
    var blks: ArrayBuffer[Block] = entries.map(createBlock).to(ArrayBuffer)

    val funcUuids = functionBlocks.getOrElse(uuid, Set.empty[ByteString]).to(ArrayBuffer)
    val funcblks = funcUuids.filterNot(entries.contains).map(createBlock)
    
    blks ++= funcblks


    blks = blks.flatMap(handle_long_if)

    return blks.flatMap(handle_unlifted_indirects)
  }
  

  def createBlock(uuid: ByteString): Block = {
    
    val address: Option[Int] = addresses.get(uuid)
    val semantics: ArrayBuffer[Statement] = createSemantics(uuid)
    val block = Block(Base64.getUrlEncoder().encodeToString(uuid.toByteArray()), address, semantics) // Empty Goto implies block not connected to proc, but i think these get removed somewhere
    blkCount += 1
    blkMap += (uuid -> block)
    return block
  }


  def createSemantics(uuid: ByteString): ArrayBuffer[Statement] = {
    var visitor = new SemanticsLoader(uuid, parserMap, blkCount)
    val statements = visitor.createStatements()
    return statements
  }

  // Converter between ByteString and Base64 because Gtirb is weird like that
  def get_ByteString(uuid: String): ByteString = ByteString.copyFrom(Base64.getUrlDecoder().decode(uuid))

  // Form new ByteString using old Base64label and some Int, useful for creating many small blocks
  def get_blkLabel(label: String, extraBlkCount: Int): String =  {
      var decodedBytes: Array[Byte] = Base64.getUrlDecoder().decode(label)
      decodedBytes(decodedBytes.length - 1) = (decodedBytes.last + extraBlkCount).toByte
      Base64.getUrlEncoder().encodeToString(decodedBytes)
  }

  // makes blkLabel boogie friendly 
  def convert_label(label: String): String = {
    if (label.startsWith("l_")) {
      label
    } else {
      "l_" + label.replace("=", "").replace("-", "")
    }
  }

  /** 
  * Handles the case where ddisasm fails to lift an indirect call correctly (such as blr instruction)
  * This results in a write to PC in the middle of a block. the block is split up, with the first half having the correct indirect call
  * 
  * @param blk 
  * @return An Arraybuffer contaning two blocks, that have been split from the original
  *
  */
  def handle_unlifted_indirects(blk: Block): ArrayBuffer[Block] = {
    
    var block = blk
    val blkBuffer = ArrayBuffer.newBuilder[Block]
    var stmts_without_jump = block.statements.dropRight(1)

    while (stmts_without_jump.exists {elem => elem.isInstanceOf[LocalAssign] && elem.asInstanceOf[LocalAssign].lhs.name == "_PC"} ) {
      extraBlkCount += 1
      val unliftedJmp = block.statements.find {elem => elem.isInstanceOf[LocalAssign] && elem.asInstanceOf[LocalAssign].lhs.name == "_PC" }.get
      val endStmts = block.statements.splitOn(unliftedJmp)
      val startStmts = block.statements
      
      
      
      val startBlk = Block(block.label, block.address, startStmts)
      val endBlk = Block(get_blkLabel(block.label, extraBlkCount), block.address, endStmts)
      

      // Adds relevant edge to startBlock, replacing write to PC
      edgeMap += (endBlk.label -> edgeMap.get(startBlk.label).get)
      val callEdge = proto.CFG.Edge(get_ByteString(startBlk.label), get_ByteString(endBlk.label), Option(proto.CFG.EdgeLabel(false, false, proto.CFG.EdgeType.Type_Call)))
      val fallEdge = proto.CFG.Edge(get_ByteString(startBlk.label), get_ByteString(endBlk.label), Option(proto.CFG.EdgeLabel(false, false, proto.CFG.EdgeType.Type_Fallthrough)))
      edgeMap(startBlk.label) = ArrayBuffer(callEdge, fallEdge)
      blkMap += (get_ByteString(endBlk.label) -> endBlk)
      blkMap(get_ByteString(startBlk.label)) = startBlk
      
      blkBuffer ++= ArrayBuffer(startBlk)
      block = endBlk
      stmts_without_jump = endBlk.statements.dropRight(1)
    }
    
    blkBuffer += block
    val blks = blkBuffer.result()
    if (!blks.isEmpty) {
      return blks
    } else {
      return ArrayBuffer[Block](blk)
    }
  }

  /** 
  * Handles the case where an if-else chain appears in the middle of a block. 
  * In this case, the block is split into two, before and after the occurance of this IF. 
  *
  * Additionally, several trueBlocks(blocks containing stmts that are to be executed if the condition preceding is true)
  *                    and falseBlocks(blocks containing GoTos to the next condition if the previous condition was false)
  * Need to be created.
  *
  * @return: An ArrayBuffer containing the new blocks, or an arraybuffer containing just the original block if no if-else chain appears
  *
  */
  def handle_long_if(blk: Block): ArrayBuffer[Block] = { //NOTE: This will only handle ONE longif per block curently. Will probably need to put a while loop around it to continously check endBlk

    val create_TempIf: Expr => TempIf = conds => TempIf(false, ArrayBuffer(conds), ArrayBuffer[ArrayBuffer[Statement]]())

    val create_endEdge: (String, String) => proto.CFG.Edge = (uuid, endUuid) =>  
        proto.CFG.Edge(get_ByteString(uuid), get_ByteString(endUuid), Option(proto.CFG.EdgeLabel(false, true, proto.CFG.EdgeType.Type_Fallthrough)))

    if (blk.statements.exists {elem =>  elem.isInstanceOf[TempIf] && elem.asInstanceOf[TempIf].isLongIf}) {
      
      // Split Blk in two and remove IfStmt
      val ifStmt = blk.statements.find {elem => elem.isInstanceOf[TempIf] && elem.asInstanceOf[TempIf].isLongIf}.get.asInstanceOf[TempIf]

      val endStmts = blk.statements.splitOn(ifStmt)
      val startStmts = blk.statements
      startStmts.remove(ifStmt)
      startStmts.append(create_TempIf(ifStmt.conds.remove(0)))


      val startBlk = Block(blk.label, blk.address, startStmts)
      val endBlk = Block(get_blkLabel(blk.label, extraBlkCount), blk.address, endStmts)
      edgeMap += (endBlk.label -> edgeMap.get(startBlk.label).get)
      extraBlkCount += 1

      blkMap(get_ByteString(startBlk.label)) = startBlk
      blkMap += (get_ByteString(endBlk.label) -> endBlk)

      // falseBlock creation
      val tempFalseBlks: ArrayBuffer[Block] = ifStmt.conds.map { stmts => 
        val label = get_blkLabel(blk.label, extraBlkCount)
        val block = Block(label, blk.address, ArrayBuffer(create_TempIf(stmts)))
        extraBlkCount = 1 
        block
      }
      

      // trueBlock creation
      val trueBlks: ArrayBuffer[Block] = ifStmt.stmts.map { stmts =>
        val label = get_blkLabel(blk.label, extraBlkCount)
        val block = Block(label, blk.address, stmts)

        val edge = create_endEdge(label, endBlk.label)
        edgeMap += (label -> ArrayBuffer(edge))
        blkMap += (get_ByteString(label) -> block)
        extraBlkCount += 1 
        block
      }

      // Adds Else to FalseBlocks
      val label = get_blkLabel(blk.label, extraBlkCount)
      val elseBlk = Block(label, blk.address, ArrayBuffer(ifStmt.elseStatement.get))

      val edge = create_endEdge(label, endBlk.label)
      edgeMap += (label -> ArrayBuffer(edge))
      blkMap += (get_ByteString(elseBlk.label) -> elseBlk)
      val falseBlks = (startBlk +: tempFalseBlks.toList).to(ArrayBuffer) += elseBlk
      extraBlkCount += 1


      // Adds relevant edges to falseBlocks, so that extra blocks can be added when jumps are parsed
      for (i <- 0 until falseBlks.size - 1) {
        val ifEdge = proto.CFG.Edge(get_ByteString(falseBlks(i).label), get_ByteString(trueBlks(i).label), Option(proto.CFG.EdgeLabel(false, false, proto.CFG.EdgeType.Type_Branch))) 
        val fallEdge = proto.CFG.Edge(get_ByteString(falseBlks(i).label), get_ByteString(falseBlks(i + 1).label), Option(proto.CFG.EdgeLabel(false, false, proto.CFG.EdgeType.Type_Fallthrough)))
        edgeMap(falseBlks(i).label) = ArrayBuffer(fallEdge, ifEdge)
        blkMap += (get_ByteString(falseBlks(i).label) -> falseBlks(i))
      }

      return falseBlks ++ trueBlks ++ ArrayBuffer(endBlk)
    
    } else {
      ArrayBuffer[Block](blk)
    }
    
  }

  // Handles the case where a block has one outgoing edge using gtirb cfg labelling
  def singleJump(procedures: ArrayBuffer[Procedure], block: Block, edge: proto.CFG.Edge, 
                  entries: List[ByteString], blocks: List[ByteString]): Jump = {

    val label = edge.label.get

    label.`type` match {

      case proto.CFG.EdgeType.Type_Fallthrough => 
        return GoTo(ArrayBuffer[Block](blkMap(edge.targetUuid)), None)
      
      case proto.CFG.EdgeType.Type_Call => 

        if (label.direct) {
          val proc = get_proc(edge.targetUuid, procedures)
          return DirectCall(proc, None, Option(proc.name))
        } else {
          return IndirectCall(get_jmp_reg(block.statements.last), None, None) 
        }
      
      case proto.CFG.EdgeType.Type_Branch => 

        if (entries.contains(edge.targetUuid)) {
          val proc = get_proc(edge.targetUuid, procedures)
          return DirectCall(proc, None, Option(proc.name)) //TODO: This really should be a DirectJump, since branch instruction doesn't push to stack

        } else if ((blocks.contains(edge.targetUuid) && !entries.contains(edge.targetUuid))) {
          return GoTo(ArrayBuffer[Block](blkMap(edge.targetUuid)), None)

        } else {
          return IndirectCall(get_jmp_reg(block.statements.last), None, None) //ditto above todo but IndirectJump
        }
      
      case proto.CFG.EdgeType.Type_Return => 
        return IndirectCall(get_jmp_reg(block.statements.last), None, None) 
      

      case _ => ???
    }

  }

  // Ditto above, but handles the case where a block has more than one outgoing edge 
  def multiJump(procedures: ArrayBuffer[Procedure], block: Block, edges: ArrayBuffer[proto.CFG.Edge], 
                entries: List[ByteString], ifStmt: Statement): Either[Jump, ArrayBuffer[Block]] = {
   
    val types = edges.map(_.label.get.`type`)

    val hasFunctionReturn = types.contains(proto.CFG.EdgeType.Type_Call) 
                            && types.contains(proto.CFG.EdgeType.Type_Fallthrough)

    val hasConditionalBranch = types.contains(proto.CFG.EdgeType.Type_Branch) 
                                && types.contains(proto.CFG.EdgeType.Type_Fallthrough)

    (hasFunctionReturn, hasConditionalBranch) match {

      case (true, false) => //Function return and fallthrough to next block 
        val callEdge = edges.find(_.label.get.`type` 
                                  == proto.CFG.EdgeType.Type_Call).get
        val fallEdge = edges.find(_.label.get.`type` 
                                  == proto.CFG.EdgeType.Type_Fallthrough).get

        if (callEdge.label.get.direct) {
          val targetUuid = callEdge.targetUuid
          val proc = get_proc(targetUuid, procedures)
          Left(DirectCall(proc, Option(blkMap(fallEdge.targetUuid)), Option(proc.name)))
        } else {
          Left(IndirectCall(get_jmp_reg(block.statements.last), Option(blkMap(fallEdge.targetUuid)), None))
        }

      case (false, true) => //If statement, need to create TRUE and FALSE blocks that contain asserts
        val blks = ArrayBuffer[Block]()
        val cond: Statement = Assume(ifStmt.asInstanceOf[TempIf].conds(0), checkSecurity=true)
        val notCond = Assume(UnaryExpr(BoolNOT, ifStmt.asInstanceOf[TempIf].conds(0)), checkSecurity=true) // Inverted Condition
        edges.foreach { elem => 
          elem.label.get.`type` match {
            case proto.CFG.EdgeType.Type_Branch =>
              blks += Block(convert_label(block.label + "_TRUE"), None, ArrayBuffer(cond), 
                            GoTo(ArrayBuffer(blkMap(elem.targetUuid)) , None))

            case proto.CFG.EdgeType.Type_Fallthrough =>
              blks += Block(convert_label(block.label + "_FALSE"), None, ArrayBuffer(notCond), 
                              GoTo(ArrayBuffer(blkMap(elem.targetUuid)) , None))
              
            
            case _ => ???

          }
        }
        Right(blks)


      case _ => ???
    }

  }

  // Blanket createJumps function that calls the above two as neccessary, as well as stripping temporary statements and superfluous blocks 
  def createJumps(procedures: ArrayBuffer[Procedure]): ArrayBuffer[Procedure] = {
    val cpy = procedures
    val entries = functionEntries.values.flatten.toList
    val blocks = functionBlocks.values.flatten.toList

    for (p <- procedures) {
      var extraBlocks = ArrayBuffer[Block]()
      var superfluousBlocks = ArrayBuffer[Block]()
      for (b <- p.blocks) {

        if (edgeMap.contains(b.label)) {
          // Block has outgoing edges, call jump functions

          val edges = edgeMap(b.label)

          if (edges.size > 1) {
            multiJump(cpy, b, edges, entries, b.statements(b.statements.size - 1)) match {
              case Left(jump) =>
                b.replaceJump(jump)
              case Right(blks) =>
                extraBlocks ++= blks
                b.replaceJump(GoTo(blks, None))
            }
          } else {
            val edge = edges(0)
            b.replaceJump(singleJump(cpy, b, edge, entries, blocks))
          }
        } else {
          //Block has no outgoing edges, check for incoming edges. 
          if (!incomingEdgeMap.contains(b.label)) {
            superfluousBlocks += b //No incoming or outgoing edge, remove
          }

        }

        b.statements.lastOption match { // remove "_PC" statement
          case Some(LocalAssign(lhs: Register, _, _)) if lhs.name == "_PC" =>
             b.statements.remove(b.statements.lastElem.get) 
          case Some(TempIf(_, _, _, _, _)) => // remove tempIF statement
            b.statements.remove(b.statements.lastElem.get) 
          case _ => // do Nothing
        }
        b.label = convert_label(b.label) // convert into boogie friendly format
      }
      p.removeBlocks(superfluousBlocks)
      p.addBlocks(extraBlocks)    
    }

    return procedures
  }

}
