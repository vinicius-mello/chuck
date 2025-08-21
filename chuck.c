#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>

typedef struct {
	const char * str;
	int64_t len;
} substr;

substr substr_null() {
	substr r = { .str = 0, .len = -1};
	return r;
}

int substr_isempty(substr s) {
	return s.str !=0 && s.len ==0;
}

substr substr_init(const char * s) {
	substr r = { .str = s, .len = strlen(s)};
	return r;
}

int substr_in(char c, substr s) {
	for(int i=0;i<s.len;++i) 
		if(c==s.str[i]) return 1;
	return 0;
}

int substr_equal(substr sa, substr sb) {
	if(sa.len != sb.len) return 0;
	for(int i=0;i<sa.len;++i) 
		if(sa.str[i]!=sb.str[i]) return 0;
	return 1;
}

void substr_print(substr s, int quote) {
	if(quote) printf("'");
	for(int i=0; i<s.len; ++i) printf("%c", s.str[i]);
	if(quote) printf("'");
}

substr substr_next(substr s, substr last, substr delim) {
	substr r;
	const char * p = s.str;
	int i = last.str==0 ? 0 : (last.str - p) + last.len + 1;
	while(i<s.len && substr_in(p[i], delim)) ++i;
	r.str = &p[i];
	while(i<s.len && !substr_in(p[i], delim)) ++i;
	r.len = (&p[i] - r.str);
	return r;
}

substr symbol;
substr stream;
substr delim = {.str=" \t\n\r", .len = 4};

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

static cell * state;
static int64_t here = 1;
static int64_t code = 1;
static int64_t text = 128;
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
#define PRIM_EXEC ( 12 | FLAG_PRIMITIVE )
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
  {"exec", PRIM_EXEC},
  {"here", PRIM_HERE},
  {"text", PRIM_TEXT},
  {"immediate", PRIM_IMMEDIATE},
  {"0branch", PRIM_ZERO_BRANCH},
  {"R>", PRIM_FROM_RETURN},
  {">R", PRIM_TO_RETURN},
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
};

#define MAX_DATA 4096
static cell data[MAX_DATA];

#define MAX_PROGRAM 4096
static cell program[MAX_PROGRAM];

#define MAX_STRINGS 4096
static char strings[MAX_STRINGS];

pair_int newSymbol() {
  pair_int r;
	char * p = &strings[text]; 
  r.a = text;
	r.b = symbol.len;
  strncpy(p, symbol.str, symbol.len);
  text = text+r.b;
  return r;
}

void fill_dict() {
	int64_t prev = 0;
	for(int i=0; i<sizeof(dictionary)/sizeof(dict_entry);++i) {
		dict_entry e = dictionary[i];
		latest = here;
		pair_int pi;
		pi.b = strlen(e.symbol);
		pi.a = text;
	  strncpy(&strings[pi.a], e.symbol, pi.b);
		text += pi.b; 
		int64_t tok = e.address;
		//printf("%s %llx %ld\n", e.symbol, tok, prev);
		data[here++] = (cell) tok;
		data[here++] = (cell) pi;
		data[here++] = (cell) prev;
		prev = latest;
	}
}

int64_t lookup(substr s) {
	int64_t r = latest;
	do {
		pair_int pi = data[r+1].pi;
		substr t = {.str = &strings[pi.a], .len = pi.b};
		if(substr_equal(s, t)) break;
		r = data[r+2].i;
	} while(r);
	//substr_print(s,0);
	//printf(" %ld\n", r);
	return r;
}

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

#define compile(x) (program[code++] = (cell)(x))

void exec(int64_t t) {
	int64_t a, b; 
  cell ca, cb;
 	dict_entry * e;
	pair_int pi;
	substr s;
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
		case PRIM_FIND: {
				int64_t r = latest;
				pi = POP(dataStack).pi;
				s.str = &strings[pi.a];
				s.len = pi.b;
				do {
					pi = data[r+1].pi;
					substr t = {.str = &strings[pi.a], .len = pi.b};
					if(substr_equal(s, t)) break;
					r = data[r+2].i;
				} while(r);
				PUSH(dataStack, r);
			}
			break;
		case PRIM_EXEC:
      PUSH(returnStack, ip);
			a = POP(dataStack).i;
			if(a & FLAG_PRIMITIVE) exec(a);
      else {
			  ip = a & CLEAR_FLAGS;
        call();
			}
			ip = POP(returnStack).i;
			break;
		case PRIM_COLON:
		  (*state).i = 1;
			_here = here;
			_text = text;
			_code = code;
  		symbol = substr_next(stream, symbol, delim);
			data[here++] = (cell) code;
			data[here++] = (cell) newSymbol();
			data[here++] = (cell) latest;
			break;
		case PRIM_DOT:
		  printf("%lld", POP(dataStack));
			break;
		case PRIM_REVEAL:
			latest = _here;
			break;
		case PRIM_SEMICOLON:
		  compile((int64_t)PRIM_EXIT);
  		latest = _here;
			(*state).i = 0;  
			break;
		case PRIM_CREATE:
		  _here = here;
		  symbol = substr_next(stream, symbol, delim);
  		data[here++] = (cell) code;
			data[here++] = (cell) newSymbol();
			data[here++] = (cell) latest;
			compile((int64_t)PRIM_LIT);
  		compile(here);
  		compile((int64_t)PRIM_EXIT);
  		compile((int64_t)PRIM_EXIT);
  		latest = _here;
			break;
		case PRIM_DOES:
  		a = data[latest].i & CLEAR_FLAGS;
  		program[a+2].i = PRIM_BRANCH;
  		program[a+3].i = ip + 2;
			break;
		case PRIM_COMP:
		  compile(program[++ip]);
			break;
		case PRIM_COMPILE:
		  compile(POP(dataStack));
			break;
		case PRIM_POSTPONE:
		  symbol = substr_next(stream, symbol, delim);
  		compile((int64_t)PRIM_COMP);
  		compile(data[lookup(symbol)]);
			break;
		case PRIM_ZERO_BRANCH:
		  if(POP(dataStack).i == 0) {
    		ip = program[ip+1].i-1;
  		} else ++ip;
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
  		printf("%c", (char) a);
			break;
		case PRIM_TYPE:
  		pi = POP(dataStack).pi;
  		s.len = pi.b;
			s.str = &strings[pi.a];
  		substr_print(s, 0);
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
		case PRIM_PARSE: {
		  symbol = substr_next(stream, symbol, delim);
  		char c = (char) POP(dataStack).i;
  		const char * p = symbol.str;
  		char * q = &strings[text];
  		int64_t l = 0;
  		while(*p!=c) {
    		*q++ = *p++;
    		l++;
  		}
  		symbol.str = p-1;
  		symbol.len = 1;
  		pair_int pi = { .a=text, .b=l};  
  		PUSH(dataStack, pi);
		}
		break;
		case PRIM_DUP:
		  PUSH(dataStack, TOP(dataStack));
			break;
		case PRIM_DROP:
		  POP(dataStack);
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
	}
}

void interpreter(const char * input) {
  stream = substr_init(input);
	symbol = substr_null();
	while(symbol = substr_next(stream, symbol, delim),
		!substr_isempty(symbol))	{
    int64_t e = lookup(symbol);
    if(e) {
      cell addr = data[e];
      int64_t immediate = addr.i & FLAG_IMMEDIATE;
      if((*state).i&&(!immediate))
        compile(addr.i);
      else {
        if(addr.i & FLAG_PRIMITIVE) exec(addr.i);
        else {
          ip = addr.i & CLEAR_FLAGS;
          call();
        }
      }
    } else {
      int64_t n = strtol(symbol.str, 0, 10);
      if((*state).i) {
        compile((int64_t)PRIM_LIT);
        compile(n);
      } else
        PUSH(dataStack, n);
    }
  }
}

char * words[] = {
  ": ( 41 parse drop ; immediate",
	": state 0 ;",
  ": bl 32 ;",
  ": [ 0 state ! ; immediate",
  ": ] 1 state ! ; immediate",
	": ' bl parse find @ ;",
	": literal postpone (lit) compile ;",
  ": over 1 pick ;",
	": rot >R swap R> swap ;",
  ": +! dup @ over + swap ! drop ;",
  ": ++ 1 swap +! ;",
  ": -- -1 swap +! ;",
  ": cr 13 emit 10 emit ;", 
  ": if postpone 0branch >mark postpone exit ; immediate",
  ": then <resolve ; immediate",
  ": else postpone branch >mark postpone exit swap <resolve ; immediate",
  ": begin >mark postpone branch dup 4 + compile\
     postpone branch postpone exit ; immediate",
  ": leave postpone branch over 2 + compile ; immediate",
  ": again postpone branch dup compile 3 + <resolve ; immediate",
  ": variable create 0 , does> ;",
  ": does> postpone (does>) postpone exit ; immediate",
  ": constant create , does> @ ;",
  ": fact reveal dup 1 < if drop 1 else dup 1 - fact * then ;",
  ": char bl parse unpack drop c@ ;",
  ": [char] char literal ; immediate",
  ": .\" state @ if [char] \" parse unpack dup allot\" pack \
    literal postpone type else [char] \" parse type then ; immediate", 
  ": hello begin .\" Hello! \" cr 1 - dup 0 = if leave then again drop ;"
};

int main() {
  state = &data[0];
  (*state).i = 0;
	fill_dict();
	for(int i=0; i<sizeof(words)/sizeof(char *); ++i) {
    interpreter(words[i]);
		substr_print(stream, 1);
		printf("\n");
  }
  while(1) {
    fgets(&strings[0], 128, stdin);
    interpreter(&strings[0]);
    printf(" ok\n");
  }
  return 0;
}
