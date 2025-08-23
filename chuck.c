#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <ctype.h>

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
#define PUSH(S,V) (assert((S##Top)<MAX_STACK),(S)[(++S##Top)] = (cell)(V))
#define POP(S) (assert((S##Top)>=0),(S)[(S##Top)--])
#define DROP(S) (assert((S##Top)>=0),(S##Top)--)
#define TOP(S) ((S)[(S##Top)])
#define LEN(S) ((S##Top)+1)

#define SCREEN_SIZE (16*64)

static cell * state;
static int64_t here = 1;
static int64_t code = 1;
static int64_t text = SCREEN_SIZE;
static int64_t _here;
static int64_t _code;
static int64_t _text;
static int64_t ip;


#define FLAG_PRIMITIVE (1LL << 63)
#define FLAG_IMMEDIATE (1LL << 62)
#define CLEAR_FLAGS (~(FLAG_IMMEDIATE | FLAG_PRIMITIVE))

#define PRIM_EXIT ( 0 | FLAG_PRIMITIVE ) 
#define PRIM_ADD ( 1 | FLAG_PRIMITIVE )
#define PRIM_SUB ( 2 | FLAG_PRIMITIVE )
#define PRIM_MUL ( 3 | FLAG_PRIMITIVE )
#define PRIM_SWAP ( 4 | FLAG_PRIMITIVE )
#define PRIM_PICK ( 5 | FLAG_PRIMITIVE )
#define PRIM_LIT ( 6 | FLAG_PRIMITIVE )
#define PRIM_FIND ( 7 | FLAG_PRIMITIVE )
#define PRIM_FETCH ( 8 | FLAG_PRIMITIVE )
#define PRIM_CFETCH ( 9 | FLAG_PRIMITIVE )
#define PRIM_STORE ( 10 | FLAG_PRIMITIVE )
#define PRIM_QUIT ( 11 | FLAG_PRIMITIVE )
#define PRIM_EXECUTE ( 12 | FLAG_PRIMITIVE )
#define PRIM_HERE ( 13 | FLAG_PRIMITIVE )
#define PRIM_TEXT ( 14 | FLAG_PRIMITIVE )
#define PRIM_IMMEDIATE ( 15 | FLAG_PRIMITIVE )
#define PRIM_COLON ( 16 | FLAG_PRIMITIVE | FLAG_IMMEDIATE )
#define PRIM_DOT ( 17 | FLAG_PRIMITIVE )
#define PRIM_REVEAL ( 18 | FLAG_PRIMITIVE | FLAG_IMMEDIATE )
#define PRIM_SEMICOLON ( 19 | FLAG_PRIMITIVE | FLAG_IMMEDIATE )
#define PRIM_CREATE ( 20 | FLAG_PRIMITIVE )
#define PRIM_DOES ( 21 | FLAG_PRIMITIVE )
#define PRIM_ALLOT ( 22 | FLAG_PRIMITIVE )
#define PRIM_ALLOT_STR ( 23 | FLAG_PRIMITIVE )
#define PRIM_COMP ( 24 | FLAG_PRIMITIVE )
#define PRIM_COMPILE ( 25 | FLAG_PRIMITIVE )
#define PRIM_POSTPONE ( 26 | FLAG_PRIMITIVE | FLAG_IMMEDIATE )
#define PRIM_ZERO_BRANCH ( 27 | FLAG_PRIMITIVE )
#define PRIM_BRANCH ( 28 | FLAG_PRIMITIVE )
#define PRIM_FROM_RETURN ( 29 | FLAG_PRIMITIVE )
#define PRIM_TO_RETURN ( 30 | FLAG_PRIMITIVE )
#define PRIM_MARK ( 31 | FLAG_PRIMITIVE )
#define PRIM_RESOLVE ( 32 | FLAG_PRIMITIVE )
#define PRIM_EMIT ( 33 | FLAG_PRIMITIVE )
#define PRIM_TYPE ( 34 | FLAG_PRIMITIVE )
#define PRIM_COMMA ( 35 | FLAG_PRIMITIVE )
#define PRIM_EQUAL ( 36 | FLAG_PRIMITIVE )
#define PRIM_LESSER_THAN ( 37 | FLAG_PRIMITIVE )
#define PRIM_GREATER_THAN ( 38 | FLAG_PRIMITIVE )
#define PRIM_PARSE ( 39 | FLAG_PRIMITIVE )
#define PRIM_DUP ( 40 | FLAG_PRIMITIVE )
#define PRIM_DROP ( 41 | FLAG_PRIMITIVE )
#define PRIM_PACK ( 42 | FLAG_PRIMITIVE )
#define PRIM_UNPACK ( 43 | FLAG_PRIMITIVE )
#define PRIM_ENTRY ( 44 | FLAG_PRIMITIVE )
#define PRIM_DIV ( 45 | FLAG_PRIMITIVE )
#define PRIM_MOD ( 46 | FLAG_PRIMITIVE )

typedef struct dict_entry {
  char * symbol;
  int64_t address;
} dict_entry;

static int64_t latest;

static dict_entry dictionary[] = {
  {"exit", PRIM_EXIT},
  {"(lit)", PRIM_LIT},  
  {"find", PRIM_FIND},  
  {"+", PRIM_ADD},
  {"-", PRIM_SUB},
  {"@", PRIM_FETCH},
  {"c@", PRIM_CFETCH},
  {"!", PRIM_STORE},
  {":", PRIM_COLON},
  {";", PRIM_SEMICOLON},
  {".", PRIM_DOT},
  {"reveal", PRIM_REVEAL},   
  {"quit", PRIM_QUIT},  
  {"postpone", PRIM_POSTPONE},
  {"(comp)", PRIM_COMP},
  {"compile", PRIM_COMPILE},
  {"exec", PRIM_EXECUTE},
  {"here", PRIM_HERE},
  {"text", PRIM_TEXT},
  {"immediate", PRIM_IMMEDIATE},
  {"0branch", PRIM_ZERO_BRANCH},
  {"r>", PRIM_FROM_RETURN},
  {">r", PRIM_TO_RETURN},
  {">mark", PRIM_MARK},
  {"<resolve", PRIM_RESOLVE},
  {"emit", PRIM_EMIT},
  {"type", PRIM_TYPE},
  {"branch", PRIM_BRANCH}, 
  {"swap", PRIM_SWAP},
  {"pick", PRIM_PICK},
  {"create", PRIM_CREATE},
  {",", PRIM_COMMA},
  {"allot", PRIM_ALLOT},
  {"allot\"", PRIM_ALLOT_STR},
  {"(does>)", PRIM_DOES},
  {"=", PRIM_EQUAL},
  {"<", PRIM_LESSER_THAN},
  {">", PRIM_GREATER_THAN},
  {"parse", PRIM_PARSE},
  {"dup", PRIM_DUP},
  {"drop", PRIM_DROP},
  {"*", PRIM_MUL},
  {"pack", PRIM_PACK},
  {"unpack", PRIM_UNPACK},
  {"entry", PRIM_ENTRY},
  {"/", PRIM_DIV},
  {"mod", PRIM_MOD},
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
		int64_t tok = e.address;
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
	strings[text+l] = 0;
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
	int64_t a, b; 
  cell ca, cb;
	pair_int pi;
	switch(t) {
		case PRIM_EXIT:
	  	ip = POP(returnStack).i;
			break;
		case PRIM_ADD:
  		a = POP(dataStack).i;
  		b = POP(dataStack).i;
  		PUSH(dataStack, b+a);
			break;
		case PRIM_SUB: 
  		a = POP(dataStack).i;
  		b = POP(dataStack).i;
  		PUSH(dataStack, b-a);
			break;
		case PRIM_MUL:
			a = POP(dataStack).i;
			b = POP(dataStack).i;
			PUSH(dataStack, b*a);
			break;    
		case PRIM_SWAP:
		  ca = POP(dataStack);
  		cb = POP(dataStack);
  		PUSH(dataStack, ca);
  		PUSH(dataStack, cb);
			break;
		case PRIM_PICK:
  		a = POP(dataStack).i;
  		PUSH(dataStack, dataStack[dataStackTop-a]);
			break;
		case PRIM_LIT:
  		PUSH(dataStack, program[++ip].i);
			break;
		case PRIM_FETCH:
  		a = POP(dataStack).i;
  		PUSH(dataStack, data[a]);
			break;
		case PRIM_CFETCH:
		  a = POP(dataStack).i;
  		PUSH(dataStack, (int64_t)strings[a]);
			break;
		case PRIM_STORE:
  		a = POP(dataStack).i;
  		cb = POP(dataStack);
  		data[a] = cb;
			break;
		case PRIM_QUIT:
		  exit(0);
			break;
		case PRIM_HERE:
		  PUSH(dataStack, here);
			break;
		case PRIM_TEXT:
		  PUSH(dataStack, text);
			break;
		case PRIM_IMMEDIATE:
		  data[latest].i |= FLAG_IMMEDIATE;
			break;
		case PRIM_FIND: 
			find();
			break;
		case PRIM_EXECUTE:
      PUSH(returnStack, ip);
			execute();
			ip = POP(returnStack).i;
			break;
		case PRIM_ENTRY: 
		  entry(); 
			break;
		case PRIM_COLON:
		  (*state).i = 1;
			entry();
			break;
		case PRIM_DOT:
		  printf("%lld", POP(dataStack));
			break;
		case PRIM_REVEAL:
			reveal();
			break;
		case PRIM_SEMICOLON:
		  compile(PRIM_EXIT);
			(*state).i = 0;  
  		reveal();
			break;
		case PRIM_CREATE:
		  entry();
			compile(PRIM_LIT);
  		compile(here);
  		compile(PRIM_EXIT);
  		compile(PRIM_EXIT);
  		reveal();
			break;
		case PRIM_DOES:
  		a = data[latest].i & CLEAR_FLAGS;
  		program[a+2].i = PRIM_BRANCH;
  		program[a+3].i = ip + 2;
			break;
		case PRIM_COMP:
		  compile(program[++ip].i);
			break;
		case PRIM_COMPILE:
		  compile(POP(dataStack).i);
			break;
		case PRIM_POSTPONE:
			PUSH(dataStack, (int64_t)32);
			parse();
		  find();
			compile(PRIM_COMP);
  		compile(data[POP(dataStack).i].i);
			break;
		case PRIM_ZERO_BRANCH:
		  if(POP(dataStack).i == 0)
    		ip = program[ip+1].i-1;
  		else ++ip;
			break;
		case PRIM_BRANCH:
		  ip = program[ip+1].i-1;
			break;
		case PRIM_FROM_RETURN:
		  PUSH(dataStack, POP(returnStack));
			break;
		case PRIM_TO_RETURN:
  		PUSH(returnStack, POP(dataStack));
			break;
		case PRIM_MARK:
		  PUSH(dataStack, code);
			break;
		case PRIM_RESOLVE:
			a = POP(dataStack).i;
  		program[a].i = code;
			break;
		case PRIM_EMIT:
			a = POP(dataStack).i;
  		putchar((char) a);
			break;
		case PRIM_TYPE:
  		pi = POP(dataStack).pi;
  		str_print(pi, 0);
			break;
		case PRIM_COMMA:
  		ca = POP(dataStack);
  		data[here++] = ca;
			break;
		case PRIM_ALLOT:
  		a = POP(dataStack).i;
  		here += a;
			break;
		case PRIM_ALLOT_STR:
			a = POP(dataStack).i;
			text += a;
			break;
		case PRIM_EQUAL:
  		a = POP(dataStack).i;
  		b = POP(dataStack).i;
  		PUSH(dataStack, (int64_t)(b == a));
			break;
		case PRIM_LESSER_THAN:
		  a = POP(dataStack).i;
		  b = POP(dataStack).i;
		  PUSH(dataStack, (int64_t)(b < a));
			break;
		case PRIM_GREATER_THAN:
		  a = POP(dataStack).i;
  		b = POP(dataStack).i;
  		PUSH(dataStack, (int64_t)(b > a));
			break;
		case PRIM_PARSE: 
			parse();
			break;
		case PRIM_DUP:
		  PUSH(dataStack, TOP(dataStack));
			break;
		case PRIM_DROP:
		  DROP(dataStack);
			break;
		case PRIM_PACK:
  		b = POP(dataStack).i;
  		a = POP(dataStack).i;
  		pi.a = (int32_t)a;
			pi.b = (int32_t)b;
  		PUSH(dataStack, pi);
			break;
		case PRIM_UNPACK:
		  pi = POP(dataStack).pi;
  		PUSH(dataStack, (int64_t) pi.a);
  		PUSH(dataStack, (int64_t) pi.b);
			break;
		case PRIM_DIV:
		  a = POP(dataStack).i;
		  b = POP(dataStack).i;
		  PUSH(dataStack, (b / a));
			break;
		case PRIM_MOD:
		  a = POP(dataStack).i;
		  b = POP(dataStack).i;
		  PUSH(dataStack, (b % a));
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
			int64_t n = strtol(b, &e, 10);
      if((*state).i) {
        compile(PRIM_LIT);
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
	": literal postpone (lit) compile ; ",
  ": over >r dup r> swap ; ",
	": rot >r swap r> swap ; ",
	": tuck swap over ; ",
  ": nip swap drop ; ",
  ": +! dup @ rot + swap ! ; ",
  ": ++ 1 swap +! ; ",
  ": -- -1 swap +! ; ",
  ": cr 13 emit 10 emit ; ", 
  ": if postpone 0branch >mark postpone exit ; immediate ",
  ": then <resolve ; immediate ",
  ": else postpone branch >mark postpone exit swap <resolve ; immediate ",
  ": begin >mark ; immediate ",
  ": again postpone branch compile ; immediate ",
  ": variable create 0 , does> ; ",
  ": does> postpone (does>) postpone exit ; immediate ",
  ": constant create , does> @ ; ",
  ": fact reveal dup 1 < if drop 1 else dup 1 - fact * then ; ",
  ": char bl parse unpack drop c@ ; ",
  ": [char] char literal ; immediate ",
  ": .\" state @ if [char] \" parse unpack dup allot\" pack \
    literal postpone type else [char] \" parse type then ; immediate ", 
  ": 0< 0 < ; ",
	": 0= 0 = ; ",
	": 0> 0 > ; ",
	": 1- 1 - ; ",
	": 1+ 1 + ; ",
	": hello begin .\" Hello! \" cr 1- dup 0= if drop exit then again ; ",
	": negate -1 * ; ",
	": abs dup 0< if negate then ; ",
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
