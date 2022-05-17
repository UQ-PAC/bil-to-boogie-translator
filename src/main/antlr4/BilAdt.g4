grammar BilAdt;

file : adt EOF;

adt : exp
    | term
    | endian
    | unimplemented
    | list
    | tuple
    | tid;


exp : 'Load' OPEN_PAREN var=exp COMMA exp COMMA endian COMMA NUM CLOSE_PAREN                #expLoad
    | 'Store' OPEN_PAREN var=exp COMMA exp COMMA exp COMMA endian COMMA NUM CLOSE_PAREN     #expStore
    | BINOP OPEN_PAREN exp COMMA exp CLOSE_PAREN                                        #expBinop
    | UOP OPEN_PAREN exp CLOSE_PAREN                                                    #expUop
    | 'Var' OPEN_PAREN name=STRING COMMA type CLOSE_PAREN                                    #expVar
    | 'Int' OPEN_PAREN NUM COMMA NUM CLOSE_PAREN                                        #expIntAdt
    | CAST OPEN_PAREN NUM COMMA exp CLOSE_PAREN                                         #expCast
    | 'Extract' OPEN_PAREN NUM COMMA NUM COMMA exp CLOSE_PAREN                          #expExtract
    | 'Concat' OPEN_PAREN                                                               #expConcat
    | STRING                                                                            #expString
    | NUM                                                                               #expNum
    | REGISTER                                                                          #expRegister
    ;

term : def
     | call
     | jmp
     | sub
     ;

jmp : basejmp
    | call
    | gotoSym
    ;

gotoSym : 'Goto' OPEN_PAREN tid COMMA attrs=adt COMMA cond=exp COMMA target=label CLOSE_PAREN;
sub : 'Sub' OPEN_PAREN tid COMMA attrs=adt COMMA name=STRING COMMA args COMMA blks CLOSE_PAREN;

blks : 'Blks' OPEN_PAREN OPEN_BRACKET (blk (COMMA blk)*)? CLOSE_BRACKET CLOSE_PAREN;
blk : 'Blk' OPEN_PAREN tid COMMA attrs=adt COMMA phis COMMA defs COMMA jmps CLOSE_PAREN;

phis : 'Phis' OPEN_PAREN OPEN_BRACKET (phi (COMMA phi)*)? CLOSE_BRACKET CLOSE_PAREN;
defs : 'Defs' OPEN_PAREN OPEN_BRACKET (def (COMMA def)*)? CLOSE_BRACKET CLOSE_PAREN;
jmps : 'Jmps' OPEN_PAREN OPEN_BRACKET (jmp (COMMA jmp)*)? CLOSE_BRACKET CLOSE_PAREN;
args : 'Args' OPEN_PAREN OPEN_BRACKET (arg (COMMA arg)*)? CLOSE_BRACKET CLOSE_PAREN;

phi : 'Phi' OPEN_PAREN tid COMMA attrs=adt COMMA lhs=adt COMMA values=adt CLOSE_PAREN;
basejmp : 'Jmp' OPEN_PAREN tid COMMA attrs=adt COMMA cond=exp COMMA target=adt CLOSE_PAREN;

arg : 'Arg' OPEN_PAREN tid COMMA attrs=adt COMMA lhs=exp COMMA rhs=exp COMMA intent CLOSE_PAREN;

intent : 'In' OPEN_PAREN CLOSE_PAREN | 'Out' OPEN_PAREN CLOSE_PAREN | 'Both' OPEN_PAREN CLOSE_PAREN;

endian : ENDIAN OPEN_PAREN CLOSE_PAREN;

// Load(mem, idx, endian, size)
// BINOP(exp1, exp2) -- e.g. PLUS(exp1, exp2)

// UOP(exp) -- e.g. NOT(exp1)

// var(name, type)

// Int(num, size)

// CAST(size, expr) -- e.g. UNSIGNED(size, expr)

// Let(var, val, expr) -- Unimplemented

// Unknown(string, type) -- Unimplemented

// Ite(cond, if_true, if_false) -- Unimplemented

// Extract(hb, lb, exp)
//extract : ;

// Concat(lhs, rhs) -- Unimplemented

type : imm | mem;

imm : 'Imm' OPEN_PAREN NUM CLOSE_PAREN;

mem : 'Mem' OPEN_PAREN NUM COMMA NUM CLOSE_PAREN;

// 'Tid'(number, name)
tid : 'Tid' OPEN_PAREN NUM COMMA STRING CLOSE_PAREN;

// 'Def'(
def : 'Def' OPEN_PAREN tid COMMA adt COMMA exp COMMA exp CLOSE_PAREN; // this is an assignment, they're called defs in the ADT.
call : 'Call' OPEN_PAREN tid COMMA attrs=adt COMMA undocumented=adt COMMA OPEN_PAREN calee=label COMMA returnSym=label? CLOSE_PAREN CLOSE_PAREN;

list : OPEN_BRACKET sequence CLOSE_BRACKET;

tuple : OPEN_PAREN ((adt COMMA) | (adt (COMMA adt)+))  CLOSE_PAREN;

/* Unimportant ADTs - should be matched last */
unimplemented : SYMBOL OPEN_PAREN sequence CLOSE_PAREN;

sequence : (adt (COMMA adt)*)?;

label : direct | indirect;

direct : 'Direct' OPEN_PAREN tid CLOSE_PAREN;

indirect : 'Indirect' OPEN_PAREN exp CLOSE_PAREN;

BINOP : PLUS
      | MINUS
      | TIMES
      | DIVIDE
      | SDIVIDE
      | MOD
      | SMOD
      | LSHIFT
      | RSHIFT
      | ARSHIFT
      | AND
      | OR
      | XOR
      | EQ
      | NEQ
      | LT
      | LE
      | SLT
      | SLE;

UOP : NEG | NOT;

CAST : UNSIGNED | SIGNED | HIGH | LOW;

UNSIGNED : 'UNSIGNED';
SIGNED : 'SIGNED';
HIGH : 'HIGH';
LOW : 'LOW';

// BinOp alternatives
PLUS     : 'PLUS';
MINUS    : 'MINUS';
TIMES    : 'TIMES';
DIVIDE   : 'DIVIDE';
SDIVIDE  : 'SDIVIDE';
MOD      : 'MOD';
SMOD     : 'SMOD';
LSHIFT   : 'LSHIFT';
RSHIFT   : 'RSHIFT';
ARSHIFT  : 'ARSHIFT';
AND      : 'AND';
OR       : 'OR';
XOR      : 'XOR';
EQ       : 'EQ';
NEQ      : 'NEQ';
LT       : 'LT';
LE       : 'LE';
SLT      : 'SLT';
SLE      : 'SLE';

// UnOp alternatives
NOT      : 'NOT';
NEG      : 'NEG';

ENDIAN : LITTLE_ENDIAN | BIG_ENDIAN;
LITTLE_ENDIAN : 'LittleEndian';
BIG_ENDIAN : 'BigEndian';

// Numbers and symbols
SYMBOL : ALPHA+;
ALPHA : [A-Za-z];
NUM : DEC | HEX;
DEC : DIGIT+;
HEX : '0x'? HEXDIGIT+;
REGISTER : 'R' DEC;
DIGIT : [0-9];
HEXDIGIT : [0-9a-fA-F];

// Delimiters
OPEN_PAREN : '(';
CLOSE_PAREN : ')';
COMMA : ',';
OPEN_BRACKET : '[';
CLOSE_BRACKET : ']';


// Strings
ESCAPE : '\\' ( '"' | '\\' | 'n' | 'x');
STRING :  '"' ( ESCAPE | ~('"' | '\\' | '\n' | '\r') )+ '"' ;

// Ignored
NEWLINE : '\r'? '\n' -> skip;
WHITESPACE : ' '+ -> skip;
COMMENT : '//' ~[\r\n]* -> skip;
