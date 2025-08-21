#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>

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
