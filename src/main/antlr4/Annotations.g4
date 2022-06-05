grammar Annotations;
/**
This was initially in Bil.g4, but I thought it would make more sense to have the annotations as its own file.
*/

/**
  The grammar which follows this is used to specify the program
*/
progSpec: (lpreds | gammas | lattice | rely)* ;

lpreds : 'L:' lpred (',' lpred)* ;
lpred :  (var MAPSTO secExpr);
gammas : 'GAMMA:' gamma (',' gamma)* ;
gamma :  (var MAPSTO ID);
lattice : 'Lattice:' lattice_elem (',' lattice_elem)* ;
lattice_elem : ID '<:' 'ID'* ;
rely: 'Rely:' pred ;

pred :
    pred predBop pred  # predBinOp
    | '(' pred ')'        # predBracket
    | uop pred            # predUniOp
    // TODO i dont think this is right
    | exp expComp exp     # predExprComp
    // | predLit             # predLiteral
    | GAMMA_ID            # gammaVar
    ;



predBop : AND | OR | NEQ_PRED | EQ_PRED ;
expComp : NEQ_PRED | EQ_PRED | GE | GT | LE | LT ;

secExpr :
	'if' pred 'then' secExpr 'else' secExpr #secITE
	| ID 		  # secLatticeElem
	;

exp : '(' exp ')'                                       # expBracket
    | literal                                           # expLiteral
    | var                                               # expVar
    | uop exp                                           # expUop
    | exp bop exp                                       # expBop
    | exp 'with' '[' exp ',' ENDIAN ']:' nat '<-' exp   # expStore
    | exp 'with' '[' exp ']' '<-' exp                   # expStore8 // sizes can be ommited if storing a single byte
    | CAST ':' nat '[' exp ']'                          # expCast
    // TODO maybe merge these instead??
    | exp '[' exp ',' ENDIAN ']:' nat                   # expLoad
    | exp '[' exp ']'                                   # expLoad8
    | 'extract' ':' nat ':' nat '[' exp ']'             # expExtract
	| functionName'(' argList ')'						# expFunctionCall
    ;

argList : exp (',' exp)* ;

var : ID ;
functionName : ID | '.'ID ;

bop : PLUS | MINUS | TIMES | DIVIDE | MODULO | LSL | LSR | ASR | BAND | BOR | BXOR | EQ | NEQ | LT | LE | UNKNOWN_OP ;
uop : NOT ;

nat : (NAT | NUMBER) ;
addr : NUMBER ;
literal : NUMBER ;


GAMMA_ID : 'Gamma_'ID ;
// PRIME_VAR : (ID | GAMMA_ID)'\''; // TODO
// predLit : TRUE | FALSE ;

HIGH : 'HIGH' ;
LOW : 'LOW' ;
CAST : ('pad' | 'extend' | 'high' | 'low') ;
NAT : ('u32' | 'u64') ;
ENDIAN : ('el' | 'be');
ID : (ALPHA|'_'|'#') (ALPHA | NUMBER | '_')* ;
NUMBER : HEX | DECIMAL;
DECIMAL : [0-9]+ ;
HEX : '0x'? ([0-9]|[a-f]|[A-F])+ ;
ALPHA : ([A-Z]|[a-z])+ ;
NEWLINE : '\r'? '\n' -> skip;
WHITESPACE : ' '+ -> skip;
COMMENT : '//' ~[\r\n]* -> skip;
AND : '&&' ;
OR : '||' ;
NEQ_PRED : '!=' ;
EQ_PRED : '==' ;
GT: '>' ;
GE: '>=' ;
MAPSTO : '->' ;
PLUS : '+' ;
MINUS : '-' ;
TIMES : '*' ;
DIVIDE : '/' ;
MODULO : '%' ;
LSL : '<<' ; // Inferred
LSR : '>>' ; // Inferred
ASR : '>>>' ; // Inferred
BAND : '&' ;
BOR : '|' ;
BXOR : 'xor' ;
EQ : '=' ;
NEQ : '<>' ;
LT : '<' ;
LE : '<=' ;
NOT : '~' ;
UNKNOWN_OP : '~>>' ;
