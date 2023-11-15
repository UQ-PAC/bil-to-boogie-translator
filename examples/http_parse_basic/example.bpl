var {:extern} Gamma_R0: bool;
var {:extern} Gamma_R1: bool;
var {:extern} Gamma_R16: bool;
var {:extern} Gamma_R17: bool;
var {:extern} Gamma_R2: bool;
var {:extern} Gamma_R29: bool;
var {:extern} Gamma_R30: bool;
var {:extern} Gamma_R31: bool;
var {:extern} Gamma_malloc_base: [bv64]bool;
var {:extern} Gamma_malloc_count: [bv64]bool;
var {:extern} Gamma_malloc_end: [bv64]bool;
var {:extern} Gamma_mem: [bv64]bool;
var {:extern} Gamma_stack: [bv64]bool;
var {:extern} R0: bv64;
var {:extern} R1: bv64;
var {:extern} R16: bv64;
var {:extern} R17: bv64;
var {:extern} R2: bv64;
var {:extern} R29: bv64;
var {:extern} R30: bv64;
var {:extern} R31: bv64;
var {:extern} malloc_base: [bv64]bv8;
var {:extern} malloc_count: [bv64]bv8;
var {:extern} malloc_end: [bv64]bv8;
var {:extern} mem: [bv64]bv8;
var {:extern} stack: [bv64]bv8;
const {:extern} $buf_addr: bv64;
axiom ($buf_addr == 131184bv64);
const {:extern} $password_addr: bv64;
axiom ($password_addr == 131152bv64);
const {:extern} $stext_addr: bv64;
axiom ($stext_addr == 131160bv64);
function {:extern} L(memory: [bv64]bv8, index: bv64) returns (bool) {
  (if ((index == bvadd64($stext_addr, 10bv64)) || ((index == bvadd64($stext_addr, 9bv64)) || ((index == bvadd64($stext_addr, 8bv64)) || ((index == bvadd64($stext_addr, 7bv64)) || ((index == bvadd64($stext_addr, 6bv64)) || ((index == bvadd64($stext_addr, 5bv64)) || ((index == bvadd64($stext_addr, 4bv64)) || ((index == bvadd64($stext_addr, 3bv64)) || ((index == bvadd64($stext_addr, 2bv64)) || ((index == bvadd64($stext_addr, 1bv64)) || (index == bvadd64($stext_addr, 0bv64)))))))))))) then true else (if (index == $password_addr) then false else (if (index == $buf_addr) then true else false)))
}

function {:extern} {:bvbuiltin "bvadd"} bvadd64(bv64, bv64) returns (bv64);
function {:extern} {:bvbuiltin "bvlshr"} bvlshr32(bv32, bv32) returns (bv32);
function {:extern} {:bvbuiltin "bvlshr"} bvlshr64(bv64, bv64) returns (bv64);
function {:extern} {:bvbuiltin "bvmul"} bvmul64(bv64, bv64) returns (bv64);
function {:extern} {:bvbuiltin "bvsub"} bvsub64(bv64, bv64) returns (bv64);
function {:extern} {:bvbuiltin "bvule"} bvule64(bv64, bv64) returns (bool);
function {:extern} {:bvbuiltin "bvult"} bvult64(bv64, bv64) returns (bool);
function {:inline} byte_extract32_64(value: bv32, offset: bv64) returns (bv8) {
  bvlshr32(value, bvmul64(offset, 8bv64)[32:0])[8:0]
}

function {:inline} byte_extract64_64(value: bv64, offset: bv64) returns (bv8) {
  bvlshr64(value, bvmul64(offset, 8bv64))[8:0]
}

function {:extern} gamma_load32(gammaMap: [bv64]bool, index: bv64) returns (bool) {
  (gammaMap[bvadd64(index, 3bv64)] && (gammaMap[bvadd64(index, 2bv64)] && (gammaMap[bvadd64(index, 1bv64)] && gammaMap[index])))
}

function {:extern} gamma_load64(gammaMap: [bv64]bool, index: bv64) returns (bool) {
  (gammaMap[bvadd64(index, 7bv64)] && (gammaMap[bvadd64(index, 6bv64)] && (gammaMap[bvadd64(index, 5bv64)] && (gammaMap[bvadd64(index, 4bv64)] && (gammaMap[bvadd64(index, 3bv64)] && (gammaMap[bvadd64(index, 2bv64)] && (gammaMap[bvadd64(index, 1bv64)] && gammaMap[index])))))))
}

function {:extern} gamma_load8(gammaMap: [bv64]bool, index: bv64) returns (bool) {
  gammaMap[index]
}

function {:extern} gamma_store32(gammaMap: [bv64]bool, index: bv64, value: bool) returns ([bv64]bool) {
  (lambda i: bv64 :: ((if in_bounds64(index, 4bv64, i) then value else gammaMap[i])))
}

function {:extern} gamma_store64(gammaMap: [bv64]bool, index: bv64, value: bool) returns ([bv64]bool) {
  (lambda i: bv64 :: ((if in_bounds64(index, 8bv64, i) then value else gammaMap[i])))
}

function {:inline} in_bounds64_le(base: bv64, len: bv64, i: bv64) returns (bool) {
  (if bvule64(base, bvadd64(base, len)) then (bvule64(base, i) && bvult64(i, bvadd64(base, len))) else (bvule64(base, i) || bvult64(i, bvadd64(base, len))))
}

function {:extern} memory_load32_le(memory: [bv64]bv8, index: bv64) returns (bv32) {
  (memory[bvadd64(index, 3bv64)] ++ (memory[bvadd64(index, 2bv64)] ++ (memory[bvadd64(index, 1bv64)] ++ memory[index])))
}

function {:extern} memory_load64_le(memory: [bv64]bv8, index: bv64) returns (bv64) {
  (memory[bvadd64(index, 7bv64)] ++ (memory[bvadd64(index, 6bv64)] ++ (memory[bvadd64(index, 5bv64)] ++ (memory[bvadd64(index, 4bv64)] ++ (memory[bvadd64(index, 3bv64)] ++ (memory[bvadd64(index, 2bv64)] ++ (memory[bvadd64(index, 1bv64)] ++ memory[index])))))))
}

function {:extern} memory_load8_le(memory: [bv64]bv8, index: bv64) returns (bv8) {
  memory[index]
}

function {:extern} memory_store32_le(memory: [bv64]bv8, index: bv64, value: bv32) returns ([bv64]bv8) {
  (lambda i: bv64 :: ((if in_bounds64(index, 4bv64, i) then byte_extract32_64(value, bvsub64(i, index)) else memory[i])))
}

function {:extern} memory_store64_le(memory: [bv64]bv8, index: bv64, value: bv64) returns ([bv64]bv8) {
  (lambda i: bv64 :: ((if in_bounds64(index, 8bv64, i) then byte_extract64_64(value, bvsub64(i, index)) else memory[i])))
}

function {:extern} {:bvbuiltin "zero_extend 32"} zero_extend32_32(bv32) returns (bv64);
procedure {:extern} rely();
  modifies Gamma_mem, mem;
  ensures (mem == old(mem));
  ensures (Gamma_mem == old(Gamma_mem));
  free ensures (memory_load8_le(mem, 2320bv64) == 1bv8);
  free ensures (memory_load8_le(mem, 2321bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 2322bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 2323bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130504bv64) == 80bv8);
  free ensures (memory_load8_le(mem, 130505bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130506bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130507bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130508bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130509bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130510bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130511bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130512bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130513bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130514bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130515bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130516bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130517bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130518bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130519bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131032bv64) == 84bv8);
  free ensures (memory_load8_le(mem, 131033bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 131034bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131035bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131036bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131037bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131038bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131039bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131144bv64) == 72bv8);
  free ensures (memory_load8_le(mem, 131145bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131146bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 131147bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131148bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131149bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131150bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131151bv64) == 0bv8);

procedure {:extern} rely_transitive()
  modifies Gamma_mem, mem;
  ensures (mem == old(mem));
  ensures (Gamma_mem == old(Gamma_mem));
{
  call rely();
  call rely();
}

procedure {:extern} rely_reflexive();

procedure {:extern} guarantee_reflexive();
  modifies Gamma_mem, mem;

procedure #free();
  modifies Gamma_R16, Gamma_R17, R16, R17;
  requires (forall i : int, j: bv64 :: malloc_base[i] == R0 && (bvuge64(j, R0) && bvult64(j,  malloc_end[i])) ==> Gamma_mem[j]);
  free requires (memory_load8_le(mem, 2320bv64) == 1bv8);
  free requires (memory_load8_le(mem, 2321bv64) == 0bv8);
  free requires (memory_load8_le(mem, 2322bv64) == 2bv8);
  free requires (memory_load8_le(mem, 2323bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130504bv64) == 80bv8);
  free requires (memory_load8_le(mem, 130505bv64) == 8bv8);
  free requires (memory_load8_le(mem, 130506bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130507bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130508bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130509bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130510bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130511bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130512bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130513bv64) == 8bv8);
  free requires (memory_load8_le(mem, 130514bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130515bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130516bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130517bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130518bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130519bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131032bv64) == 84bv8);
  free requires (memory_load8_le(mem, 131033bv64) == 8bv8);
  free requires (memory_load8_le(mem, 131034bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131035bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131036bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131037bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131038bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131039bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131144bv64) == 72bv8);
  free requires (memory_load8_le(mem, 131145bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131146bv64) == 2bv8);
  free requires (memory_load8_le(mem, 131147bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131148bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131149bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131150bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131151bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 2320bv64) == 1bv8);
  free ensures (memory_load8_le(mem, 2321bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 2322bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 2323bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130504bv64) == 80bv8);
  free ensures (memory_load8_le(mem, 130505bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130506bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130507bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130508bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130509bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130510bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130511bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130512bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130513bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130514bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130515bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130516bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130517bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130518bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130519bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131032bv64) == 84bv8);
  free ensures (memory_load8_le(mem, 131033bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 131034bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131035bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131036bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131037bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131038bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131039bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131144bv64) == 72bv8);
  free ensures (memory_load8_le(mem, 131145bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131146bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 131147bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131148bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131149bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131150bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131151bv64) == 0bv8);

procedure main()
  modifies Gamma_R0, Gamma_R1, Gamma_R16, Gamma_R17, Gamma_R2, Gamma_R29, Gamma_R30, Gamma_R31, Gamma_malloc_base, Gamma_malloc_count, Gamma_malloc_end, Gamma_mem, Gamma_stack, R0, R1, R16, R17, R2, R29, R30, R31, malloc_base, malloc_count, malloc_end, mem, stack;
  requires (gamma_load8(Gamma_mem, $password_addr) == false);
  requires malloc_count == 0;
  requires gamma_load32(Gamma_mem, memory_load64_le(mem, $stext_addr));
  requires R31 == 100bv64;
  free requires (memory_load8_le(mem, 131136bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131137bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131138bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131139bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131140bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131141bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131142bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131143bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131144bv64) == 72bv8);
  free requires (memory_load8_le(mem, 131145bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131146bv64) == 2bv8);
  free requires (memory_load8_le(mem, 131147bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131148bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131149bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131150bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131151bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131152bv64) == 7bv8);
  free requires (memory_load8_le(mem, 131153bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131154bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131155bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131156bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131157bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131158bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131159bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131160bv64) == 108bv8);
  free requires (memory_load8_le(mem, 131161bv64) == 107bv8);
  free requires (memory_load8_le(mem, 131162bv64) == 97bv8);
  free requires (memory_load8_le(mem, 131163bv64) == 106bv8);
  free requires (memory_load8_le(mem, 131164bv64) == 100bv8);
  free requires (memory_load8_le(mem, 131165bv64) == 108bv8);
  free requires (memory_load8_le(mem, 131166bv64) == 107bv8);
  free requires (memory_load8_le(mem, 131167bv64) == 97bv8);
  free requires (memory_load8_le(mem, 131168bv64) == 106bv8);
  free requires (memory_load8_le(mem, 131169bv64) == 100bv8);
  free requires (memory_load8_le(mem, 131170bv64) == 97bv8);
  free requires (memory_load8_le(mem, 2320bv64) == 1bv8);
  free requires (memory_load8_le(mem, 2321bv64) == 0bv8);
  free requires (memory_load8_le(mem, 2322bv64) == 2bv8);
  free requires (memory_load8_le(mem, 2323bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130504bv64) == 80bv8);
  free requires (memory_load8_le(mem, 130505bv64) == 8bv8);
  free requires (memory_load8_le(mem, 130506bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130507bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130508bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130509bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130510bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130511bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130512bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130513bv64) == 8bv8);
  free requires (memory_load8_le(mem, 130514bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130515bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130516bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130517bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130518bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130519bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131032bv64) == 84bv8);
  free requires (memory_load8_le(mem, 131033bv64) == 8bv8);
  free requires (memory_load8_le(mem, 131034bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131035bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131036bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131037bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131038bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131039bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131144bv64) == 72bv8);
  free requires (memory_load8_le(mem, 131145bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131146bv64) == 2bv8);
  free requires (memory_load8_le(mem, 131147bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131148bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131149bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131150bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131151bv64) == 0bv8);
  free ensures (Gamma_R29 == old(Gamma_R29));
  free ensures (Gamma_R31 == old(Gamma_R31));
  free ensures (R29 == old(R29));
  free ensures (R31 == old(R31));
  free ensures (memory_load8_le(mem, 2320bv64) == 1bv8);
  free ensures (memory_load8_le(mem, 2321bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 2322bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 2323bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130504bv64) == 80bv8);
  free ensures (memory_load8_le(mem, 130505bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130506bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130507bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130508bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130509bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130510bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130511bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130512bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130513bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130514bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130515bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130516bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130517bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130518bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130519bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131032bv64) == 84bv8);
  free ensures (memory_load8_le(mem, 131033bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 131034bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131035bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131036bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131037bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131038bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131039bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131144bv64) == 72bv8);
  free ensures (memory_load8_le(mem, 131145bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131146bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 131147bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131148bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131149bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131150bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131151bv64) == 0bv8);
{
  var #4: bv64;
  var Gamma_#4: bool;
  lmain:
    assume {:captureState "lmain"} true;
    #4, Gamma_#4 := bvadd64(R31, 18446744073709551584bv64), Gamma_R31;
    stack, Gamma_stack := memory_store64_le(stack, #4, R29), gamma_store64(Gamma_stack, #4, Gamma_R29);
    assume {:captureState "%0000035c"} true;
    stack, Gamma_stack := memory_store64_le(stack, bvadd64(#4, 8bv64), R30), gamma_store64(Gamma_stack, bvadd64(#4, 8bv64), Gamma_R30);
    assume {:captureState "%00000362"} true;
    R31, Gamma_R31 := #4, Gamma_#4;
    R29, Gamma_R29 := R31, Gamma_R31;
    stack, Gamma_stack := memory_store64_le(stack, bvadd64(R31, 24bv64), 0bv64), gamma_store64(Gamma_stack, bvadd64(R31, 24bv64), true);
    assume {:captureState "%00000373"} true;
    stack, Gamma_stack := memory_store64_le(stack, bvadd64(R31, 16bv64), 0bv64), gamma_store64(Gamma_stack, bvadd64(R31, 16bv64), true);
    assume {:captureState "%0000037a"} true;
    R0, Gamma_R0 := 11bv64, true;
    R30, Gamma_R30 := 2156bv64, true;
    call malloc();
    goto l00000389;
  l00000389:
    assume {:captureState "l00000389"} true;
    R1, Gamma_R1 := R0, Gamma_R0;
    R0, Gamma_R0 := 131072bv64, true;
    R0, Gamma_R0 := bvadd64(R0, 112bv64), Gamma_R0;
    call rely();
    assert (L(mem, R0) ==> Gamma_R1);
    mem, Gamma_mem := memory_store64_le(mem, R0, R1), gamma_store64(Gamma_mem, R0, Gamma_R1);
    assume {:captureState "%000003a0"} true;
    R0, Gamma_R0 := 131072bv64, true;
    R0, Gamma_R0 := bvadd64(R0, 112bv64), Gamma_R0;
    call rely();
    R2, Gamma_R2 := memory_load64_le(mem, R0), (gamma_load64(Gamma_mem, R0) || L(mem, R0));
    R0, Gamma_R0 := 131072bv64, true;
    R1, Gamma_R1 := bvadd64(R0, 88bv64), Gamma_R0;
    R0, Gamma_R0 := R2, Gamma_R2;
    call rely();
    R2, Gamma_R2 := memory_load64_le(mem, R1), (gamma_load64(Gamma_mem, R1) || L(mem, R1));
    call rely();
    assert (L(mem, R0) ==> Gamma_R2);
    mem, Gamma_mem := memory_store64_le(mem, R0, R2), gamma_store64(Gamma_mem, R0, Gamma_R2);
    assume {:captureState "%000003d2"} true;
    call rely();
    R1, Gamma_R1 := zero_extend32_32(memory_load32_le(mem, bvadd64(R1, 7bv64))), (gamma_load32(Gamma_mem, bvadd64(R1, 7bv64)) || L(mem, bvadd64(R1, 7bv64)));
    call rely();
    assert (L(mem, bvadd64(R0, 7bv64)) ==> Gamma_R1);
    mem, Gamma_mem := memory_store32_le(mem, bvadd64(R0, 7bv64), R1[32:0]), gamma_store32(Gamma_mem, bvadd64(R0, 7bv64), Gamma_R1);
    assume {:captureState "%000003e1"} true;
    R0, Gamma_R0 := 131072bv64, true;
    R0, Gamma_R0 := bvadd64(R0, 112bv64), Gamma_R0;
    call rely();
    R0, Gamma_R0 := memory_load64_le(mem, R0), (gamma_load64(Gamma_mem, R0) || L(mem, R0));
    R30, Gamma_R30 := 2228bv64, true;
    call puts();
    goto l000003fd;
  l000003fd:
    assume {:captureState "l000003fd"} true;
    R0, Gamma_R0 := 131072bv64, true;
    R0, Gamma_R0 := bvadd64(R0, 112bv64), Gamma_R0;
    call rely();
    R0, Gamma_R0 := memory_load64_le(mem, R0), (gamma_load64(Gamma_mem, R0) || L(mem, R0));
    R0, Gamma_R0 := bvadd64(R0, 1bv64), Gamma_R0;
    stack, Gamma_stack := memory_store64_le(stack, bvadd64(R31, 24bv64), R0), gamma_store64(Gamma_stack, bvadd64(R31, 24bv64), Gamma_R0);
    assume {:captureState "%0000041b"} true;
    R0, Gamma_R0 := 131072bv64, true;
    R0, Gamma_R0 := bvadd64(R0, 112bv64), Gamma_R0;
    call rely();
    R0, Gamma_R0 := memory_load64_le(mem, R0), (gamma_load64(Gamma_mem, R0) || L(mem, R0));
    R2, Gamma_R2 := 11bv64, true;
    R1, Gamma_R1 := 1bv64, true;
    R30, Gamma_R30 := 2272bv64, true;
    call memset();
    goto l00000441;
  l00000441:
    assume {:captureState "l00000441"} true;
    R0, Gamma_R0 := 131072bv64, true;
    R0, Gamma_R0 := bvadd64(R0, 112bv64), Gamma_R0;
    call rely();
    R0, Gamma_R0 := memory_load64_le(mem, R0), (gamma_load64(Gamma_mem, R0) || L(mem, R0));
    R30, Gamma_R30 := 2288bv64, true;
    call #free();
    goto l0000045b;
  l0000045b:
    assume {:captureState "l0000045b"} true;
    R0, Gamma_R0 := 0bv64, true;
    R29, Gamma_R29 := memory_load64_le(stack, R31), gamma_load64(Gamma_stack, R31);
    R30, Gamma_R30 := memory_load64_le(stack, bvadd64(R31, 8bv64)), gamma_load64(Gamma_stack, bvadd64(R31, 8bv64));
    R31, Gamma_R31 := bvadd64(R31, 32bv64), Gamma_R31;
    return;
}

procedure malloc();
  modifies Gamma_R0, Gamma_R16, Gamma_R17, Gamma_malloc_base, Gamma_malloc_count, Gamma_malloc_end, R0, R16, R17, malloc_base, malloc_count, malloc_end;
  requires bvugt64(R0, 0bv64);
  requires Gamma_R0 == true;
  free requires (memory_load8_le(mem, 2320bv64) == 1bv8);
  free requires (memory_load8_le(mem, 2321bv64) == 0bv8);
  free requires (memory_load8_le(mem, 2322bv64) == 2bv8);
  free requires (memory_load8_le(mem, 2323bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130504bv64) == 80bv8);
  free requires (memory_load8_le(mem, 130505bv64) == 8bv8);
  free requires (memory_load8_le(mem, 130506bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130507bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130508bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130509bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130510bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130511bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130512bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130513bv64) == 8bv8);
  free requires (memory_load8_le(mem, 130514bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130515bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130516bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130517bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130518bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130519bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131032bv64) == 84bv8);
  free requires (memory_load8_le(mem, 131033bv64) == 8bv8);
  free requires (memory_load8_le(mem, 131034bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131035bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131036bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131037bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131038bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131039bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131144bv64) == 72bv8);
  free requires (memory_load8_le(mem, 131145bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131146bv64) == 2bv8);
  free requires (memory_load8_le(mem, 131147bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131148bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131149bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131150bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131151bv64) == 0bv8);
  ensures ((memory_load64_le(mem, $buf_addr) == old(memory_load64_le(mem, $buf_addr))) && (memory_load8_le(mem, $password_addr) == old(memory_load8_le(mem, $password_addr))));
  ensures Gamma_R0 == true;
  ensures malloc_count == old(malloc_count) + 1;
  ensures bvugt64(malloc_end[malloc_count], malloc_base[malloc_count]);
  ensures R0 == malloc_base[malloc_count];
  ensures malloc_end[malloc_count] == bvadd64(R0, old(R0));
  ensures (forall i: int :: i != malloc_count ==> bvugt64(malloc_base[malloc_count], malloc_end[i]) || bvult64(malloc_end[malloc_count], malloc_base[i]));
  ensures (forall i: int :: i != malloc_count ==> malloc_base[i] == old(malloc_base[i]) && malloc_end[i] == old(malloc_end[i]));
  ensures bvuge64(R0, 100000000bv64);
  ensures (forall i : bv64 :: (bvuge64(i, R0) && bvult64(i, bvadd64(R0, old(R0)))) ==> (Gamma_mem[i] && gamma_load8(Gamma_mem, i)));
  free ensures (memory_load8_le(mem, 2320bv64) == 1bv8);
  free ensures (memory_load8_le(mem, 2321bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 2322bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 2323bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130504bv64) == 80bv8);
  free ensures (memory_load8_le(mem, 130505bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130506bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130507bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130508bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130509bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130510bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130511bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130512bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130513bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130514bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130515bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130516bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130517bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130518bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130519bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131032bv64) == 84bv8);
  free ensures (memory_load8_le(mem, 131033bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 131034bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131035bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131036bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131037bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131038bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131039bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131144bv64) == 72bv8);
  free ensures (memory_load8_le(mem, 131145bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131146bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 131147bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131148bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131149bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131150bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131151bv64) == 0bv8);

procedure memset();
  modifies Gamma_R16, Gamma_R17, Gamma_mem, R16, R17, mem;
  requires Gamma_R1;
  free requires (memory_load8_le(mem, 2320bv64) == 1bv8);
  free requires (memory_load8_le(mem, 2321bv64) == 0bv8);
  free requires (memory_load8_le(mem, 2322bv64) == 2bv8);
  free requires (memory_load8_le(mem, 2323bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130504bv64) == 80bv8);
  free requires (memory_load8_le(mem, 130505bv64) == 8bv8);
  free requires (memory_load8_le(mem, 130506bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130507bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130508bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130509bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130510bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130511bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130512bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130513bv64) == 8bv8);
  free requires (memory_load8_le(mem, 130514bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130515bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130516bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130517bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130518bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130519bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131032bv64) == 84bv8);
  free requires (memory_load8_le(mem, 131033bv64) == 8bv8);
  free requires (memory_load8_le(mem, 131034bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131035bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131036bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131037bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131038bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131039bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131144bv64) == 72bv8);
  free requires (memory_load8_le(mem, 131145bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131146bv64) == 2bv8);
  free requires (memory_load8_le(mem, 131147bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131148bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131149bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131150bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131151bv64) == 0bv8);
  ensures ((memory_load64_le(mem, $buf_addr) == old(memory_load64_le(mem, $buf_addr))) && (memory_load8_le(mem, $password_addr) == old(memory_load8_le(mem, $password_addr))));
  ensures (forall i: bv64 :: (Gamma_mem[i] == if (bvule64(R0, i) && bvult64(i,bvadd64(R0, R2))) then Gamma_R1 else old(gamma_load8(Gamma_mem, i))));
  ensures (forall i: bv64 :: (mem[i] == if (bvule64(R0, i) && bvult64(i,bvadd64(R0, R2))) then R1[8:0] else old(memory_load8_le(mem, i))));
  free ensures (memory_load8_le(mem, 2320bv64) == 1bv8);
  free ensures (memory_load8_le(mem, 2321bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 2322bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 2323bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130504bv64) == 80bv8);
  free ensures (memory_load8_le(mem, 130505bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130506bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130507bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130508bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130509bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130510bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130511bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130512bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130513bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130514bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130515bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130516bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130517bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130518bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130519bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131032bv64) == 84bv8);
  free ensures (memory_load8_le(mem, 131033bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 131034bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131035bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131036bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131037bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131038bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131039bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131144bv64) == 72bv8);
  free ensures (memory_load8_le(mem, 131145bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131146bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 131147bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131148bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131149bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131150bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131151bv64) == 0bv8);

procedure puts();
  modifies Gamma_R16, Gamma_R17, R16, R17;
  free requires (memory_load8_le(mem, 2320bv64) == 1bv8);
  free requires (memory_load8_le(mem, 2321bv64) == 0bv8);
  free requires (memory_load8_le(mem, 2322bv64) == 2bv8);
  free requires (memory_load8_le(mem, 2323bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130504bv64) == 80bv8);
  free requires (memory_load8_le(mem, 130505bv64) == 8bv8);
  free requires (memory_load8_le(mem, 130506bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130507bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130508bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130509bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130510bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130511bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130512bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130513bv64) == 8bv8);
  free requires (memory_load8_le(mem, 130514bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130515bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130516bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130517bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130518bv64) == 0bv8);
  free requires (memory_load8_le(mem, 130519bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131032bv64) == 84bv8);
  free requires (memory_load8_le(mem, 131033bv64) == 8bv8);
  free requires (memory_load8_le(mem, 131034bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131035bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131036bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131037bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131038bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131039bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131144bv64) == 72bv8);
  free requires (memory_load8_le(mem, 131145bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131146bv64) == 2bv8);
  free requires (memory_load8_le(mem, 131147bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131148bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131149bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131150bv64) == 0bv8);
  free requires (memory_load8_le(mem, 131151bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 2320bv64) == 1bv8);
  free ensures (memory_load8_le(mem, 2321bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 2322bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 2323bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130504bv64) == 80bv8);
  free ensures (memory_load8_le(mem, 130505bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130506bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130507bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130508bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130509bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130510bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130511bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130512bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130513bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 130514bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130515bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130516bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130517bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130518bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 130519bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131032bv64) == 84bv8);
  free ensures (memory_load8_le(mem, 131033bv64) == 8bv8);
  free ensures (memory_load8_le(mem, 131034bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131035bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131036bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131037bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131038bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131039bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131144bv64) == 72bv8);
  free ensures (memory_load8_le(mem, 131145bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131146bv64) == 2bv8);
  free ensures (memory_load8_le(mem, 131147bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131148bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131149bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131150bv64) == 0bv8);
  free ensures (memory_load8_le(mem, 131151bv64) == 0bv8);
