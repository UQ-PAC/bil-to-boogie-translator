
function booltobv1(bool) returns (bv1);
axiom booltobv1(true) == 1bv1 && booltobv1(false) == 0bv1;

function bv1tobool(bv1) returns (bool);
axiom bv1tobool(1bv1) == true && bv1tobool(0bv1) == false;

// TODO signed or unsigned div
procedure malloc(size: bv64) returns (addr: bv64, Gamma_addr: bool);
ensures (forall i: bv64 :: ((bv64ule(0bv64, i) && bv64ult(i, bv64udiv(size, 4bv64))) ==> old(heap_free[bv64add(addr, i)]) == true)); 
ensures (forall i: bv64 :: ((bv64ule(0bv64, i) && bv64ult(i, bv64udiv(size, 4bv64))) ==> heap_free[bv64add(addr, i)] == false)); 
ensures heap_sizes[addr] == bv64udiv(size, 4bv64);
ensures Gamma_addr == false;

procedure free_(addr: bv64) returns ();
ensures (forall i: bv64 :: (bv64ule(0bv64, i) && bv64ult(i, bv64udiv(heap_sizes[addr], 4bv64))) ==> heap_free[bv64add(addr, i)] == true); 


/*****
 * Bitvector functions for bv1
 ****/
// Arithmetic
function {:bvbuiltin "bvadd"} bv1add(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvsub"} bv1sub(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvmul"} bv1mul(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvudiv"} bv1udiv(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvurem"} bv1urem(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvsdiv"} bv1sdiv(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvsrem"} bv1srem(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvsmod"} bv1smod(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvneg"} bv1neg(bv1) returns(bv1);

// Bitwise operations
function {:bvbuiltin "bvand"} bv1and(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvor"} bv1or(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvnot"} bv1not(bv1) returns(bv1);
function {:bvbuiltin "bvxor"} bv1xor(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvnand"} bv1nand(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvnor"} bv1nor(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvxnor"} bv1xnor(bv1,bv1) returns(bv1);

// Bit shifting
function {:bvbuiltin "bvshl"} bv1shl(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvlshr"} bv1lshr(bv1,bv1) returns(bv1);
function {:bvbuiltin "bvashr"} bv1ashr(bv1,bv1) returns(bv1);

// Unsigned comparison
function {:bvbuiltin "bvult"} bv1ult(bv1,bv1) returns(bool);
function {:bvbuiltin "bvule"} bv1ule(bv1,bv1) returns(bool);
function {:bvbuiltin "bvugt"} bv1ugt(bv1,bv1) returns(bool);
function {:bvbuiltin "bvuge"} bv1uge(bv1,bv1) returns(bool);

// Signed comparison
function {:bvbuiltin "bvslt"} bv1slt(bv1,bv1) returns(bool);
function {:bvbuiltin "bvsle"} bv1sle(bv1,bv1) returns(bool);
function {:bvbuiltin "bvsgt"} bv1sgt(bv1,bv1) returns(bool);
function {:bvbuiltin "bvsge"} bv1sge(bv1,bv1) returns(bool);

function bv1eq(x: bv1, y: bv1) returns(bool) { x == y }
function bv1neq(x: bv1, y: bv1) returns(bool) { x != y }


/*****
 * Bitvector functions for bv32
 ****/
// Arithmetic
function {:bvbuiltin "bvadd"} bv32add(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsub"} bv32sub(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvmul"} bv32mul(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvudiv"} bv32udiv(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvurem"} bv32urem(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsdiv"} bv32sdiv(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsrem"} bv32srem(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsmod"} bv32smod(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvneg"} bv32neg(bv32) returns(bv32);

// Bitwise operations
function {:bvbuiltin "bvand"} bv32and(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvor"} bv32or(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvnot"} bv32not(bv32) returns(bv32);
function {:bvbuiltin "bvxor"} bv32xor(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvnand"} bv32nand(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvnor"} bv32nor(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvxnor"} bv32xnor(bv32,bv32) returns(bv32);

// Bit shifting
function {:bvbuiltin "bvshl"} bv32shl(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} bv32lshr(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvashr"} bv32ashr(bv32,bv32) returns(bv32);

// Unsigned comparison
function {:bvbuiltin "bvult"} bv32ult(bv32,bv32) returns(bool);
function {:bvbuiltin "bvule"} bv32ule(bv32,bv32) returns(bool);
function {:bvbuiltin "bvugt"} bv32ugt(bv32,bv32) returns(bool);
function {:bvbuiltin "bvuge"} bv32uge(bv32,bv32) returns(bool);

// Signed comparison
function {:bvbuiltin "bvslt"} bv32slt(bv32,bv32) returns(bool);
function {:bvbuiltin "bvsle"} bv32sle(bv32,bv32) returns(bool);
function {:bvbuiltin "bvsgt"} bv32sgt(bv32,bv32) returns(bool);
function {:bvbuiltin "bvsge"} bv32sge(bv32,bv32) returns(bool);

function bv32eq(x: bv32, y: bv32) returns(bool) { x == y }
function bv32neq(x: bv32, y: bv32) returns(bool) { x != y }


/*****
 * Bitvector functions for bv64
 ****/
// Arithmetic
function {:bvbuiltin "bvadd"} bv64add(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsub"} bv64sub(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvmul"} bv64mul(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} bv64udiv(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvurem"} bv64urem(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsdiv"} bv64sdiv(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsrem"} bv64srem(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsmod"} bv64smod(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvneg"} bv64neg(bv64) returns(bv64);

// Bitwise operations
function {:bvbuiltin "bvand"} bv64and(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvor"} bv64or(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvnot"} bv64not(bv64) returns(bv64);
function {:bvbuiltin "bvxor"} bv64xor(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvnand"} bv64nand(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvnor"} bv64nor(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvxnor"} bv64xnor(bv64,bv64) returns(bv64);

// Bit shifting
function {:bvbuiltin "bvshl"} bv64shl(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvlshr"} bv64lshr(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvashr"} bv64ashr(bv64,bv64) returns(bv64);

// Unsigned comparison
function {:bvbuiltin "bvult"} bv64ult(bv64,bv64) returns(bool);
function {:bvbuiltin "bvule"} bv64ule(bv64,bv64) returns(bool);
function {:bvbuiltin "bvugt"} bv64ugt(bv64,bv64) returns(bool);
function {:bvbuiltin "bvuge"} bv64uge(bv64,bv64) returns(bool);

// Signed comparison
function {:bvbuiltin "bvslt"} bv64slt(bv64,bv64) returns(bool);
function {:bvbuiltin "bvsle"} bv64sle(bv64,bv64) returns(bool);
function {:bvbuiltin "bvsgt"} bv64sgt(bv64,bv64) returns(bool);
function {:bvbuiltin "bvsge"} bv64sge(bv64,bv64) returns(bool);

function bv64eq(x: bv64, y: bv64) returns(bool) { x == y }
function bv64neq(x: bv64, y: bv64) returns(bool) { x != y }

var heap: [bv64] bv8; var Gamma_heap: [bv64] bool;
var heap_free: [bv64] bool; var Gamma_heap_free: [bv64] bool;
var heap_sizes: [bv64] bv64; var Gamma_heap_sizes: [bv64] bool;
var stack: [bv64] bv8; var Gamma_stack: [bv64] bool;
const L_heap: [bv64] bool; const Gamma_L_heap: [bv64] bool;
const L_stack: [bv64] bool; const Gamma_L_stack: [bv64] bool;
var SP: bv64; var Gamma_SP: bool;
var R31: bv64; var Gamma_R31: bool;
function L(pos: bv64, heap: [bv64] bv8) returns (bool);

procedure rely(); modifies heap, Gamma_heap;
 ensures true;
 ensures (forall i: bv64 :: ((heap[i] == old(heap[i])) ==> (Gamma_heap[i] == old(Gamma_heap[i]))));

procedure main() returns (main_result: bv32, Gamma_main_result: bool) 
 modifies heap, stack, Gamma_heap, Gamma_stack, SP, R31, Gamma_SP, Gamma_R31;   {
var ZF: bv1; var Gamma_ZF: bool;
var CF: bv1; var Gamma_CF: bool;
var NF: bv1; var Gamma_NF: bool;
var VF: bv1; var Gamma_VF: bool;
var R0: bv64; var Gamma_R0: bool;
var #30: bv1; var Gamma_#30: bool;
var #28: bv64; var Gamma_#28: bool;
var R1: bv64; var Gamma_R1: bool;
var #27: bv64; var Gamma_#27: bool;
label00000246:
    call rely();
    assert true;
    R0 := 69632bv64;    // 0000010c
    Gamma_R0 := true;
    call rely();
    assert true;
    R0 := bv64add(R0, 52bv64);    // 00000110
    Gamma_R0 := Gamma_R0;
    call rely();
    assert true;
    #27 := 0bv32 ++ heap[bv64add(R0, 0bv64)] ++ heap[bv64add(R0, 1bv64)] ++ heap[bv64add(R0, 2bv64)] ++ heap[bv64add(R0, 3bv64)];    // 00000114
    Gamma_#27 := (Gamma_heap[R0] || L(R0, heap));
    call rely();
    assert true;
    R0 := 0bv64;    // 00000116
    Gamma_R0 := true;
    call rely();
    assert true;
    R0 := bv64or(bv64and(R0, 18446744069414584320bv64), #27);    // 00000118
    Gamma_R0 := (Gamma_R0 && Gamma_#27);
    call rely();
    assert true;
    #28 := R0[32:0] ++ 0bv32;    // 0000011c
    Gamma_#28 := Gamma_R0;
    call rely();
    assert true;
    NF := #28[64:63];    // 0000011e
    Gamma_NF := Gamma_#28;
    call rely();
    assert true;
    VF := bv1and(R0[32:0][32:31], bv1neg(#28[64:63]));    // 00000120
    Gamma_VF := (Gamma_R0 && Gamma_#28);
    call rely();
    assert true;
    ZF := booltobv1(bv64eq(#28, 0bv64));    // 00000122
    Gamma_ZF := Gamma_#28;
    call rely();
    assert true;
    CF := bv1and(bv1or(R0[32:0][32:31], R0[32:0][32:31]), bv1neg(bv1or(#28[64:63], bv1neg(#28[64:63]))));    // 00000124
    Gamma_CF := (Gamma_R0 && (Gamma_R0 && (Gamma_#28 && Gamma_#28)));
    call rely();
    assert true;
    #30 := bv1neg(booltobv1(bv1neq(ZF, 0bv1)));    // 0000012d
    Gamma_#30 := Gamma_ZF;
    call rely();
    assert Gamma_#30;
    if (bv1tobool(#30)) { goto label00000127; } goto label00000139;
label00000127:
    call rely();
    assert true;
    R0 := 0bv64;    // 00000130
    Gamma_R0 := true;
    call rely();
    assert true;
    R0 := bv64and(R0, 18446744069414584320bv64);    // 00000132
    Gamma_R0 := Gamma_R0;
    call rely();
    assert true;
    main_result := R0[32:0];    // generatedline
    Gamma_main_result := Gamma_R0;
    call rely();
    assert true;
    return;
label00000139:
    call rely();
    assert true;
    R0 := 69632bv64;    // 0000013b
    Gamma_R0 := true;
    call rely();
    assert true;
    R0 := bv64add(R0, 52bv64);    // 0000013f
    Gamma_R0 := Gamma_R0;
    call rely();
    assert true;
    R1 := 0bv64;    // 00000143
    Gamma_R1 := true;
    call rely();
    assert true;
    R1 := bv64or(bv64and(R1, 18446744069414584320bv64), 1bv64);    // 00000145
    Gamma_R1 := Gamma_R1;
    call rely();
    assert (L(R0, heap) ==> Gamma_R1);
    heap[bv64add(R0, 0bv64)] := R1[32:0][8:0]; heap[bv64add(R0, 1bv64)] := R1[32:0][16:8]; heap[bv64add(R0, 2bv64)] := R1[32:0][24:16]; heap[bv64add(R0, 3bv64)] := R1[32:0][32:24];     // 00000149
    Gamma_heap[R0] := Gamma_R1;
    call rely();
    assert true;
    goto label00000127;
}