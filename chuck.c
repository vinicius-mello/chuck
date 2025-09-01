#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <ctype.h>
#include <math.h>
#include <sys/time.h>

typedef struct {
  int32_t a;
  int32_t b;
} pair_int; 

typedef struct {
  float a;
  float b;
} pair_float; 

typedef union {
  int64_t i;
  double f;
  pair_int pi;
  pair_float pf;
} cell;

#define MAX_STACK 512
static cell returnStack[MAX_STACK];
static int returnStackTop = -1; 
static cell dataStack[MAX_STACK];
static int dataStackTop = -1; 
#if 0 
#define PUSH(S,V) (assert((S##Top)<MAX_STACK),(S)[(++S##Top)] = (cell)(V))
#define POP(S) (assert((S##Top)>=0),(S)[(S##Top)--])
#define DROP(S) (assert((S##Top)>=0),(S##Top)--)
#define TOP(S) ((S)[(S##Top)])
#define LEN(S) ((S##Top))
#else
#define PUSH(S,V) ((S)[(++S##Top)] = (cell)(V))
#define POP(S) ((S)[(S##Top)--])
#define DROP(S) ((S##Top)--)
#define TOP(S) ((S)[(S##Top)])
#define LEN(S) ((S##Top))
#endif

#define SCREEN_SIZE (16*64)

static cell * state;
static int64_t here = 1;
static int64_t code = 1;
static int64_t text = SCREEN_SIZE;
static int64_t _here;
static int64_t _code;
static int64_t _text;
static int64_t ip;
//register int64_t ip asm("ebx");  

#define FLAG_PRIMITIVE (1LL << 63)
#define FLAG_IMMEDIATE (1LL << 62)
#define CLEAR_FLAGS (~(FLAG_IMMEDIATE | FLAG_PRIMITIVE))

#define _EXIT          0 
#define _ADD           1 
#define _SUB           2
#define _MUL           3
#define _SWAP  			   4 
#define _PICK  	       5 
#define _LIT           6 
#define _FIND          7 
#define _FETCH         8 
#define _CFETCH        9 
#define _STORE        10 
#define _BYE         11 
#define _EXECUTE      12 
#define _HERE         13 
#define _TEXT         14 
#define _IMMEDIATE    15 
#define _COLON        16 
#define _DOT          17 
#define _REVEAL       18 
#define _SEMICOLON    19 
#define _CREATE       20 
#define _DOES         21 
#define _ALLOT        22 
#define _ALLOT_STR    23 
#define _COMP         24 
#define _COMPILE      25 
#define _POSTPONE     26 
#define _ZERO_BRANCH  27 
#define _BRANCH       28 
#define _FROM_RETURN  29 
#define _TO_RETURN    30 
#define _MARK         31 
#define _RESOLVE      32 
#define _EMIT         33 
#define _TYPE         34 
#define _COMMA        35 
#define _EQUAL        36 
#define _LESSER_THAN  37 
#define _GREATER_THAN 38 
#define _PARSE        39 
#define _DUP          40 
#define _DROP         41 
#define _PACK         42 
#define _UNPACK       43 
#define _ENTRY        44 
#define _DIV          45 
#define _MOD          46 
#define _TOP_RETURN   47 
#define _CSTORE       48 
#define _TO_FLOAT     49 
#define _FADD         50 
#define _FDOT         51 
#define _FSUB         52 
#define _FMUL         53 
#define _FDIV         54 
#define _FROM_FLOAT   55 
#define _FEXP         56 
#define _FLOG         57 
#define _FSIN         58 
#define _FCOS         59 
#define _FSQRT        60
#define _DEPTH        61
#define _MTIME        62

typedef struct dict_entry {
  char * symbol;
  int64_t address;
} dict_entry;

static int64_t latest;

static dict_entry dictionary[] = {
  {"exit", _EXIT},
  {"(lit)", _LIT},  
  {"find", _FIND},  
  {"+", _ADD},
  {"-", _SUB},
  {"@", _FETCH},
  {"c@", _CFETCH},
  {"!", _STORE},
  {":", _COLON | FLAG_IMMEDIATE},
  {";", _SEMICOLON | FLAG_IMMEDIATE},
  {".", _DOT},
  {"reveal", _REVEAL | FLAG_IMMEDIATE},   
  {"bye", _BYE},  
  {"postpone", _POSTPONE | FLAG_IMMEDIATE},
  {"(comp)", _COMP},
  {"compile", _COMPILE},
  {"exec", _EXECUTE},
  {"here", _HERE},
  {"text", _TEXT},
  {"immediate", _IMMEDIATE},
  {"0branch", _ZERO_BRANCH},
  {"r>", _FROM_RETURN},
  {">r", _TO_RETURN},
  {"r@", _TOP_RETURN},
  {">mark", _MARK},
  {"<resolve", _RESOLVE},
  {"emit", _EMIT},
  {"type", _TYPE},
  {"branch", _BRANCH}, 
  {"swap", _SWAP},
  {"pick", _PICK},
  {"create", _CREATE},
  {",", _COMMA},
  {"allot", _ALLOT},
  {"allot\"", _ALLOT_STR},
  {"(does>)", _DOES},
  {"=", _EQUAL},
  {"<", _LESSER_THAN},
  {">", _GREATER_THAN},
  {"parse", _PARSE},
  {"dup", _DUP},
  {"drop", _DROP},
  {"*", _MUL},
  {"pack", _PACK},
  {"unpack", _UNPACK},
  {"entry", _ENTRY},
  {"/", _DIV},
  {"mod", _MOD},
  {"c!", _CSTORE},
  {">f", _TO_FLOAT},
  {"f+", _FADD},
  {"f.", _FDOT},
  {"f-", _FSUB},
  {"f*", _FMUL},
  {"f/", _FDIV},
  {"<f", _FROM_FLOAT},
  {"fexp", _FEXP},
  {"flog", _FLOG},
  {"fsin", _FSIN},
  {"fcos", _FCOS},
  {"fsqrt", _FSQRT},
  {"depth", _DEPTH},
  {"mtime", _MTIME},
};

#define MAX_DATA 4096
static cell data[MAX_DATA];

#define MAX_PROGRAM 4096
static cell program[MAX_PROGRAM];

#define MAX_STRINGS 4096
static char strings[MAX_STRINGS];

void str_print(pair_int s, int quote) {
	if(quote) putchar('\'');
	for(int i=0; i<s.b; ++i) putchar(strings[s.a+i]);
	if(quote) putchar('\'');
}

int str_equal(pair_int sa, pair_int sb) {
	if(sa.b != sb.b) return 0;
	for(int i=0;i<sa.b; ++i) 
		if(strings[sa.a+i]!=strings[sb.a+i]) return 0;
	return 1;
}

pair_int str_append(pair_int s) {
  pair_int r = {.a = text, .b = s.b};
  if(s.a!=r.a) 
		strncpy(&strings[r.a], &strings[s.a], s.b);
  text = text+r.b;
  return r;
}

void init() {
	state = &data[0];
  (*state).i = 0;
	int64_t prev = 0;
	for(int i=0; i<sizeof(dictionary)/sizeof(dict_entry); ++i) {
		dict_entry e = dictionary[i];
		latest = here;
		pair_int pi = { .a = text, .b = strlen(e.symbol) };
	  strncpy(&strings[pi.a], e.symbol, pi.b);
		text += pi.b; 
		int64_t tok = e.address | FLAG_PRIMITIVE;
		data[here++] = (cell) tok;
		data[here++] = (cell) pi;
		data[here++] = (cell) prev;
		prev = latest;
	}
}

void exec(int64_t t);

void call() {
  PUSH(returnStack, (int64_t)-1);
  do {
    cell t = program[ip];
    if(t.i & FLAG_PRIMITIVE) {
      exec(t.i);
      ip++;
    } 
    else {
      PUSH(returnStack, ip);
      ip = t.i & CLEAR_FLAGS;
    }
  } while(ip!=0);
}

#define compile(x) (program[code++].i = (int64_t)(x))

void find() {
	int64_t r = latest;
	pair_int pi = POP(dataStack).pi;
	do {
		pair_int ti = data[r+1].pi;
		if(str_equal(pi, ti)) break;
			r = data[r+2].i;
	} while(r);
	PUSH(dataStack, r);
}

static int64_t in;
static int64_t ntib;

void parse() {
  char c = (char) POP(dataStack).i;
  int64_t l = 0;
  while(in<ntib && strings[in]!=c) {
		strings[text+l] = strings[in];
		l++;in++;
	}
	in += 1;
	strings[text+l] = 0; // strtoll
	while(in<ntib && isspace(strings[in])) in++;
	pair_int pi = { .a=text, .b=l };
  PUSH(dataStack, pi);
}

void entry() {
	_here = here;
  _text = text;
	_code = code;
	PUSH(dataStack, (int64_t)32);
	parse();
  data[here++] = (cell) code;
	data[here++] = (cell) str_append(POP(dataStack).pi);
	data[here++] = (cell) latest;
}

void execute() {
	int64_t a = POP(dataStack).i;
	if(a & FLAG_PRIMITIVE) exec(a);
  else {
		ip = a & CLEAR_FLAGS;
    call();
	}
}

void reveal() {
	latest = _here;
}

void exec(int64_t t) {
	t &= CLEAR_FLAGS;
	register int64_t a, b; 
  register cell ca, cb;
	pair_int pi;
	struct timeval tv;

	switch(t) {
		case _EXIT:
	  	ip = POP(returnStack).i;
			break;
		case _ADD:
  		a = POP(dataStack).i;
  		b = POP(dataStack).i;
  		PUSH(dataStack, b+a);
			break;
		case _SUB: 
  		a = POP(dataStack).i;
  		b = POP(dataStack).i;
  		PUSH(dataStack, b-a);
			break;
		case _MUL:
			a = POP(dataStack).i;
			b = POP(dataStack).i;
			PUSH(dataStack, b*a);
			break;    
		case _SWAP:
		  ca = POP(dataStack);
  		cb = POP(dataStack);
  		PUSH(dataStack, ca);
  		PUSH(dataStack, cb);
			break;
		case _PICK:
  		a = POP(dataStack).i;
  		PUSH(dataStack, dataStack[dataStackTop-a]);
			break;
		case _LIT:
  		PUSH(dataStack, program[++ip].i);
			break;
		case _FIND: 
			find();
			break;
		case _FETCH:
  		a = POP(dataStack).i;
  		PUSH(dataStack, data[a]);
			break;
		case _CFETCH:
		  a = POP(dataStack).i;
  		PUSH(dataStack, (int64_t)strings[a]);
			break;
		case _STORE:
  		a = POP(dataStack).i;
  		cb = POP(dataStack);
  		data[a] = cb;
			break;
		case _BYE:
		  exit(0);
			break;
		case _EXECUTE:
      PUSH(returnStack, ip);
			execute();
			ip = POP(returnStack).i;
			break;
		case _HERE:
		  PUSH(dataStack, here);
			break;
		case _TEXT:
		  PUSH(dataStack, text);
			break;
		case _IMMEDIATE:
		  data[latest].i |= FLAG_IMMEDIATE;
			break;
		case _COLON:
		  (*state).i = 1;
			entry();
			break;
		case _DOT:
		  printf("%lld ", POP(dataStack));
			break;
		case _REVEAL:
			reveal();
			break;
		case _SEMICOLON:
		  compile(_EXIT | FLAG_PRIMITIVE);
			(*state).i = 0;  
  		reveal();
			break;
		case _CREATE:
		  entry();
			compile(_LIT | FLAG_PRIMITIVE);
  		compile(here);
  		compile(_EXIT | FLAG_PRIMITIVE);
  		compile(_EXIT | FLAG_PRIMITIVE);
  		reveal();
			break;
		case _DOES:
  		a = data[latest].i & CLEAR_FLAGS;
  		program[a+2].i = _BRANCH | FLAG_PRIMITIVE;
  		program[a+3].i = ip + 2;
			break;
		case _ALLOT:
  		a = POP(dataStack).i;
  		here += a;
			break;
		case _ALLOT_STR:
			a = POP(dataStack).i;
			text += a;
			break;
		case _COMP:
		  compile(program[++ip].i);
			break;
		case _COMPILE:
		  compile(POP(dataStack).i);
			break;
		case _POSTPONE:
			PUSH(dataStack, (int64_t)32);
			parse();
		  find();
			compile(_COMP | FLAG_PRIMITIVE);
  		compile(data[POP(dataStack).i].i);
			break;
		case _ZERO_BRANCH:
		  if(POP(dataStack).i == 0)
    		ip = program[ip+1].i-1;
  		else ++ip;
			break;
		case _BRANCH:
		  ip = program[ip+1].i-1;
			break;
		case _FROM_RETURN:
		  PUSH(dataStack, POP(returnStack));
			break;
		case _TO_RETURN:
  		PUSH(returnStack, POP(dataStack));
			break;
		case _MARK:
		  PUSH(dataStack, code);
			break;
		case _RESOLVE:
			a = POP(dataStack).i;
  		program[a].i = code;
			break;
		case _EMIT:
			a = POP(dataStack).i;
  		putchar((char) a);
			break;
		case _TYPE:
  		pi = POP(dataStack).pi;
  		str_print(pi, 0);
			break;
		case _COMMA:
  		ca = POP(dataStack);
  		data[here++] = ca;
			break;
		case _EQUAL:
  		a = POP(dataStack).i;
  		b = POP(dataStack).i;
  		PUSH(dataStack, (int64_t)(b == a));
			break;
		case _LESSER_THAN:
		  a = POP(dataStack).i;
		  b = POP(dataStack).i;
		  PUSH(dataStack, (int64_t)(b < a));
			break;
		case _GREATER_THAN:
		  a = POP(dataStack).i;
  		b = POP(dataStack).i;
  		PUSH(dataStack, (int64_t)(b > a));
			break;
		case _PARSE: 
			parse();
			break;
		case _DUP:
		  PUSH(dataStack, TOP(dataStack));
			break;
		case _DROP:
		  DROP(dataStack);
			break;
		case _PACK:
  		b = POP(dataStack).i;
  		a = POP(dataStack).i;
  		pi.a = (int32_t)a;
			pi.b = (int32_t)b;
  		PUSH(dataStack, pi);
			break;
		case _UNPACK:
		  pi = POP(dataStack).pi;
  		PUSH(dataStack, (int64_t) pi.a);
  		PUSH(dataStack, (int64_t) pi.b);
			break;
		case _ENTRY: 
		  entry(); 
			break;
		case _DIV:
		  a = POP(dataStack).i;
		  b = POP(dataStack).i;
		  PUSH(dataStack, (b / a));
			break;
		case _MOD:
		  a = POP(dataStack).i;
		  b = POP(dataStack).i;
		  PUSH(dataStack, (b % a));
			break;
		case _TOP_RETURN:
  		PUSH(dataStack, TOP(returnStack));
			break;
		case _CSTORE:
		  a = POP(dataStack).i;
  		cb = POP(dataStack);
  		strings[a] = (char) cb.i;
			break;
		case _TO_FLOAT:
		  ca = POP(dataStack);
  		PUSH(dataStack, (double) ca.i);
			break;
		case _FADD:
		  cb = POP(dataStack);
		  ca = POP(dataStack);
  		PUSH(dataStack, ca.f+cb.f);
			break;
		case _FDOT:
		  printf("%lf ", POP(dataStack).f);
			break;
		case _FSUB:
		  cb = POP(dataStack);
		  ca = POP(dataStack);
  		PUSH(dataStack, ca.f-cb.f);
			break;
		case _FMUL:
		  cb = POP(dataStack);
		  ca = POP(dataStack);
  		PUSH(dataStack, ca.f*cb.f);
			break;
		case _FDIV:
		  cb = POP(dataStack);
		  ca = POP(dataStack);
  		PUSH(dataStack, ca.f/cb.f);
			break;
		case _FROM_FLOAT:
		  ca = POP(dataStack);
		  PUSH(dataStack, (int64_t) ca.f);
			break;
		case _FEXP:
		  ca = POP(dataStack);
		  PUSH(dataStack, exp(ca.f));
			break;
		case _FLOG:
		  ca = POP(dataStack);
		  PUSH(dataStack, log(ca.f));
			break;
		case _FSIN:
		  ca = POP(dataStack);
		  PUSH(dataStack, sin(ca.f));
			break;
		case _FCOS:
		  ca = POP(dataStack);
		  PUSH(dataStack, cos(ca.f));
			break;
		case _FSQRT:
		  ca = POP(dataStack);
		  PUSH(dataStack, sqrt(ca.f));
			break;
		case _DEPTH:
		  PUSH(dataStack, (int64_t) LEN(dataStack));
			break;
		case _MTIME:
			gettimeofday(&tv, NULL);
		  PUSH(dataStack, (int64_t) (tv.tv_usec/1000)+(tv.tv_sec*1000));
			break;
	}
}

void interpreter() {
	while(in<ntib && isspace(strings[in])) in++;
	while(in<ntib) {
		PUSH(dataStack, (int64_t)32);
		parse();
		find();
    int64_t e = POP(dataStack).i;
    if(e) {
      int64_t a = data[e].i;
      int64_t immediate = a & FLAG_IMMEDIATE;
      if((*state).i&&(!immediate))
        compile(a);
      else {
        PUSH(dataStack, a);
				execute();
      }
    } else {
			const char * b = &strings[text]; 
			char * e; 
			int64_t n = strtoll(b, &e, 10);
      if((*state).i) {
        compile(_LIT | FLAG_PRIMITIVE);
        compile(n);
      } else
        PUSH(dataStack, n);
		}
  }
}

char * words[] = {
  ": ( 41 parse drop ; immediate ",
	": state 0 ; ",
  ": bl 32 ; ",
  ": [ 0 state ! ; immediate ", 
  ": ] 1 state ! ; immediate ",
	": ' bl parse find @ ; ",
	": [compile] ' compile ; immediate ",
	": literal postpone (lit) compile ; ",
  ": over >r dup r> swap ; ",
	": rot >r swap r> swap ; ",
	": -rot swap >r swap r> ; ",
	": tuck swap over ; ",
  ": nip swap drop ; ",
	": 2dup over over ; ",
	": 2swap rot >r rot r> ; ",
	": 2drop drop drop ; ",
  ": 0< 0 < ; ",
	": 0= 0 = ; ",
	": 0> 0 > ; ",
	": not 0= ;",
	": 1- 1 - ; ",
	": 1+ 1 + ; ",
  ": +! dup @ rot + swap ! ; ",
  ": ++ 1 swap +! ; ",
  ": -- -1 swap +! ; ",
  ": cr 13 emit 10 emit ; ", 
  ": does> postpone (does>) postpone exit ; immediate ",
  ": variable create 0 , does> ; ",
  ": constant create , does> @ ; ",
	": array create allot does> + ;",
  ": if postpone 0branch >mark postpone exit ; immediate ",
  ": then <resolve ; immediate ",
  ": else postpone branch >mark postpone exit swap <resolve ; immediate ",
  ": begin >mark ; immediate ",
  ": again postpone branch compile ; immediate ",
	": until postpone 0branch compile ; immediate ",
	": while [compile] if swap ; immediate ",
	": repeat [compile] again [compile] then ; immediate ",
	"5 constant (leave-stack-max) ",
	"(leave-stack-max) array (leave-stack) ",
	"variable (ls@)  (ls@) --",
	": (>l) (ls@) ++ (ls@) @ (leave-stack) ! ;",
	": (@l) (ls@) @ (leave-stack) @ ;",
	": (l>) (@l) (ls@) -- ;",
	": do postpone pack postpone >r >mark postpone branch dup 4 + compile \
	   >mark (>l) postpone branch postpone exit ; immediate ",
	": leave postpone branch (@l) compile ; immediate",
	": (checkloop) unpack 1+ 2dup pack ; ",
	": (check+loop) unpack rot dup 0> if + 2dup else + 2dup swap 2swap then pack ; ",
	": i postpone r@ postpone unpack postpone nip ; immediate ",
	": j postpone r> postpone r> postpone dup \
	   postpone unpack postpone nip postpone -rot postpone >r postpone >r ; immediate ",
	": loop postpone r> postpone (checkloop) postpone >r postpone > [compile] if swap \
	  [compile] again [compile] then (l>) 1+ <resolve postpone r> postpone drop ; immediate ",
  ": +loop postpone r> postpone (check+loop) postpone >r postpone > [compile] if swap \
	  [compile] again [compile] then (l>) 1+ <resolve postpone r> postpone drop ; immediate ",
  ": fact reveal dup 1 < if drop 1 else dup 1 - fact * then ; ",
  ": char bl parse unpack drop c@ ; ",
  ": [char] char literal ; immediate ",
  ": .\" state @ if [char] \" parse unpack dup allot\" pack \
    literal postpone type else [char] \" parse type then ; immediate ", 
	": hello begin .\" Hello! \" cr 1- dup 0= if drop exit then again ; ",
	": negate -1 * ; ",
	": abs dup 0< if negate then ; ",
	": .s depth dup 0= if drop exit then -1 swap 1- do i pick . -1 +loop ; ",
};

int main() {
	init();
	for(int i=0; i<sizeof(words)/sizeof(char *); ++i) {
    ntib = strlen(words[i]);
		in = 0;
		strncpy(&strings[0], words[i], ntib);
		interpreter();
  }
  printf("Chuck64 v0.1\n\n ok\n");
  while(1) {
    fgets(&strings[0], SCREEN_SIZE, stdin);
    ntib = strlen(&strings[0])-1;
		in = 0;
		interpreter();
    printf(" ok\n");
  }
  return 0;
}
