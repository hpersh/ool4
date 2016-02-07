#include <stdio.h>
#include <ctype.h>

#include "ool.h"


bool
stream_eof(struct stream *str)
{
  return ((*str->funcs->eof)(str));
}

int
stream_getc(struct stream *str)
{
  return ((*str->funcs->getc)(str));
}

void
stream_ungetc(struct stream *str, char c)
{
  (*str->funcs->ungetc)(str, c);
}

bool
stream_file_eof(struct stream *str)
{
  return (feof(((struct stream_file *) str)->fp));
}

int
stream_file_getc(struct stream *str)
{
  struct stream_file *_str = (struct stream_file *) str;

  if (_str->last == '\n')  ++_str->line;

  return (_str->last = fgetc(_str->fp));
}

void
stream_file_ungetc(struct stream *str, char c)
{
  struct stream_file *_str = (struct stream_file *) str;

  if (c == '\n')  --_str->line;

  ungetc(c, _str->fp);
}

struct stream_funcs stream_funcs_file[] = {
  { .eof    = stream_file_eof,
    .getc   = stream_file_getc,
    .ungetc = stream_file_ungetc,
  }
};

void
stream_file_init(struct stream_file *str, FILE *fp)
{
  str->base->funcs = stream_funcs_file;
  str->fp          = fp;
  str->last        = 0;
  str->line        = 1;
}

unsigned 
isspecial(unsigned c)
{
  switch (c) {
  case '"':
  case '`':
  case ',':
  case '(':
  case ')':
  case '[':
  case ']':
  case '{':
  case '}':
  case '=':
  case '@':
    return (true);

  default:
    ;
  }

  return (false);
}

void
tokbuf_append(struct tokbuf *tb, unsigned n, char *s)
{
  unsigned nn = tb->len + n;
  if (nn > tb->bufsize) {
    unsigned k = round_up_to_power_of_2(nn);
    char *p = mem_alloc(k, false);
    memcpy(p, tb->buf, tb->len);
    mem_free(tb->buf, tb->bufsize);
    
    tb->bufsize = k;
    tb->buf     = p;
  }
  
  memcpy(tb->buf + tb->len, s, n);
  tb->len += n;
}

void
tokbuf_append_char(struct tokbuf *tb, char c)
{
  tokbuf_append(tb, 1, &c);
}

void
parse_error(char *fmt, ...)
{
  fprintf(stderr, "Syntax error: ");

  va_list ap;

  va_start(ap, fmt);

  vfprintf(stderr, fmt, ap);

  va_end(ap);

  struct stream *str = oolvm->inpfp->str;

  for (;;) {
    char c;

    if ((c = stream_getc(str)) < 0 || c == '\n')  break;
  }

  error(0);
}

bool
token_get(void)
{
  struct stream *str = oolvm->inpfp->str;
  struct tokbuf *tb = oolvm->inpfp->tb;
  char          c;

  tb->len = 0;

 again:
  for (;;) {
    c = stream_getc(str);
    if (c < 0)  return (false);

    if (!isspace(c))  break;
  }

  if (c == '%') {
    for (;;) {
      c = stream_getc(str);
      if (c < 0)  return (false);

      if (c == '\n')  goto again;
    }
  }
  
  tokbuf_append_char(tb, c);

  if (c == '`') {
    unsigned depth = 1;
  
    for (;;) {
      c = stream_getc(str);
      if (c < 0)  parse_error("Premature EOF\n");
      
      if (c == '`')  ++depth;
      
      if (c == '\'')  --depth;
      
      tokbuf_append_char(tb, c);
      
      if (c == '\'' && depth == 0)  return (true);
    }
  }

  if (c == '=') {
    c = stream_getc(str);

    if (c == '!') {
      tokbuf_append_char(tb, c);
    } else if (c >= 0) {
      stream_ungetc(str, c);
    }

    return (true);
  }

  if (isspecial(c))  return (true);

  for (;;) {
    c = stream_getc(str);
    if (c < 0 || isspace(c))  break;

    if (isspecial(c)) {
      stream_ungetc(str, c);
      break;
    }

    tokbuf_append_char(tb, c);
  }
  
  return (true);
}

void parse_token(inst_t *dst);

void
parse_quote(inst_t *dst)
{
  FRAME_WORK_BEGIN(1) {
    if (!parse(&WORK(0))) {
      parse_error("Premature EOF\n");
    }

    list_new(&WORK(0), WORK(0), 0);
    method_call_new(&WORK(0), consts.str_quote, WORK(0));
    inst_assign(dst, WORK(0));
  } FRAME_WORK_END;
}

void
parse_pair_or_list(inst_t *dst)
{
  struct tokbuf *tb = oolvm->inpfp->tb;
  unsigned      pairf = false;

  FRAME_WORK_BEGIN(2) {
    unsigned i;
    inst_t   *p;
  
    for (i = 0, p = &WORK(0); ; ++i) {
      if (!token_get())  parse_error("Premature EOF\n");

      if (tb->len == 1) {
	switch (tb->buf[0]) {
	case ']':
	case '}':
	  parse_error("Expected )");
	case ',':
	  if (i != 1)  parse_error("Unexpected ,\n");
	  pairf = true;
	  continue;
	case ')':
	  goto done;
	default:
	  ;
	}
      }
	
      if (pairf && i > 2)  parse_error("Malformed pair\n");

      parse_token(&WORK(1));
      list_new(p, WORK(1), 0);
      p = &CDR(*p);
    }

  done:
    if (pairf) {
      pair_new(dst, CAR(WORK(0)), CAR(CDR(WORK(0))));
    } else {
      inst_assign(dst, WORK(0));
    }
  } FRAME_WORK_END;
}

void
parse_method_call(inst_t *dst)
{
  struct tokbuf *tb = oolvm->inpfp->tb;

  FRAME_WORK_BEGIN(5) {
    unsigned i;
    inst_t   *p;

    for (i = 0, p = &WORK(1); ; ++i) {
      if (!token_get())  parse_error("Premature EOF\n");

      if (tb->len == 1) {
	switch (tb->buf[0]) {
	case ')':
	case '}':
	  parse_error("Expected ]\n");
	case ']':
	  goto got;
	default:
	  ;
	}
      }
      
      if (i & 1) {
	if (i == 1) {
	  str_newc(&WORK(0), 1, tb->len, tb->buf);
	  continue;
	}

	if (!(i == 3 && strcmp(STRVAL(WORK(0))->data, "@") == 0 && tb->len == 1 && tb->buf[0] == '='
	      || STRVAL(WORK(0))->size >= 2 && STRVAL(WORK(0))->data[STRVAL(WORK(0))->size - 2] == ':'
	      )
	    ) {
	bad_sel:
	  parse_error("Selector word must end in :\n");
	}	

	str_newc(&WORK(0), 2, STRVAL(WORK(0))->size - 1, STRVAL(WORK(0))->data,
		              tb->len, tb->buf
		 );
	continue;
      }

      parse_token(&WORK(2));      
      list_new(p, WORK(2), 0);
      p = &CDR(*p);
    }

  got:
    switch (i) {
    case 3:
      if (strcmp(STRVAL(WORK(0))->data, "=!") == 0) {
	list_new(&WORK(3), CAR(WORK(1)), 0);
	method_call_new(&WORK(3), consts.str_quote, WORK(3));
	list_new(&WORK(4), CAR(CDR(WORK(1))), 0);
	list_new(&WORK(4), WORK(3), WORK(4));
	list_new(&WORK(4), consts.cl_env, WORK(4));
	method_call_new(dst, consts.str_atc_defc, WORK(4));
	goto done;
      }
      if (strcmp(STRVAL(WORK(0))->data, "=") == 0) {
	list_new(&WORK(3), CAR(WORK(1)), 0);
	method_call_new(&WORK(3), consts.str_quote, WORK(3));
	list_new(&WORK(4), CAR(CDR(WORK(1))), 0);
	list_new(&WORK(4), WORK(3), WORK(4));
	list_new(&WORK(4), consts.cl_env, WORK(4));
	method_call_new(dst, consts.str_atc_putc, WORK(4));
	goto done;
      }
      if (strcmp(STRVAL(WORK(0))->data, "@") == 0) {
	list_new(&WORK(3), CAR(CDR(WORK(1))), 0);
	method_call_new(&WORK(3), consts.str_quote, WORK(3));
	list_new(&WORK(3), WORK(3), 0);
	list_new(&WORK(3), CAR(WORK(1)), WORK(3));
	method_call_new(dst, consts.str_atc, WORK(3));
	goto done;
      }
      break;
    case 5:
      if (strcmp(STRVAL(WORK(0))->data, "@=") == 0) {
	list_new(&WORK(3), CAR(CDR(WORK(1))), 0);
	method_call_new(&WORK(3), consts.str_quote, WORK(3));
	list_new(&WORK(4), CAR(CDR(CDR(WORK(1)))), 0);
	list_new(&WORK(4), WORK(3), WORK(4));
	list_new(&WORK(4), CAR(WORK(1)), WORK(4));
	method_call_new(dst, consts.str_atc_putc, WORK(4));
	goto done;
      }
      break;
    default:
      ;
    }

    if (!(i <= 2
	  || STRVAL(WORK(0))->size >= 2
	     && STRVAL(WORK(0))->data[STRVAL(WORK(0))->size - 2] == ':'
	  )
	) {
      goto bad_sel;
    }

    method_call_new(dst, WORK(0), WORK(1));
    
  done:
    ;
  } FRAME_WORK_END;
}

void
parse_block(inst_t *dst)
{
  struct tokbuf *tb = oolvm->inpfp->tb;

  FRAME_WORK_BEGIN(3) {
    unsigned i;
    inst_t    *p;

    for (i = 0, p = &WORK(1); ; ++i) {
      if (!token_get())  parse_error("Premature EOF\n");

      if (tb->len == 1){
	switch (tb->buf[0]) {
	case ')':
	case ']':
	  parse_error("Expected }\n");
	case '}':
	  goto done;
	default:
	  ;
	}
      }

      parse_token(&WORK(2));
      
      if (i == 0) {
	if (!is_list(WORK(2)))  parse_error("Block args must be list\n");
	
	inst_assign(&WORK(0), WORK(2));
	
	continue;
      }
      
      list_new(p, WORK(2), 0);
      p = &CDR(*p);
    }
    
  done:
    block_new(dst, WORK(0), WORK(1));
  } FRAME_WORK_END;
}

bool
tok_is_float(void)
{
  struct tokbuf *tb = oolvm->inpfp->tb;
  char     *p = tb->buf, c;
  unsigned n  = tb->len, k;

  if (n == 0)  return (false);

  if (*p == '-') {
    ++p;  --n;
  }

  for (k = 0; n > 0; --n, ++p, ++k) {
    c = *p;
    if (isdigit(c))  continue;
    if (c == '.')  goto decimal;
    if (toupper(c) == 'E')  goto exponent;
    return (false);
  }
  return (k >= 1);

 decimal:
  for (++p, --n; n > 0; --n, ++p) {
    c = *p;
    if (isdigit(c)) continue;
    if (toupper(c) == 'E')  goto exponent;
    return (false);
  }
  return (true);

 exponent:
  ++p;  --n;

  if (n == 0)  return (false);

  if (*p == '-') {
    ++p;  --n;
  }

  for (k = 0; n > 0; --n, ++p, ++k) {
    if (isdigit(*p))  continue;
    return (false);
  }
  return (k >= 1);
}

void
parse_float(inst_t *dst)
{
  struct tokbuf *tb = oolvm->inpfp->tb;
  floatval_t    val;

  tokbuf_append_char(tb, 0);
  sscanf(tb->buf, "%Lg", &val);
  float_new(dst, val);
}

bool
tok_is_int(void)
{
  struct tokbuf *tb = oolvm->inpfp->tb;
  char     *p = tb->buf, c;
  unsigned n  = tb->len, k;

  if (n > 0 && *p == '-') {
    ++p;  --n;
  }

  for (k = 0; n > 0; --n, ++p, ++k) {
    c = *p;
    if (!isdigit(c))  return (false);
  }
  return (k >= 1);
}

bool
tok_is_hex(void)
{
  struct tokbuf *tb = oolvm->inpfp->tb;
  char     *p = tb->buf, c;
  unsigned n  = tb->len, k;

  if (!(n >= 2 && p[0] == '0' && toupper(p[1]) == 'X'))  return (false);

  p += 2;  n -= 2;
  
  for (k = 0; n > 0; --n, ++p, ++k) {
    c = *p;
    if (!isxdigit(c))  return (false);
  }
  return (k >= 1);
}

void
parse_int(inst_t *dst)
{
  struct tokbuf *tb = oolvm->inpfp->tb;
  char          *fmt, *s;
  intval_t      val;

  if (tb->len >= 3 && tb->buf[0] == '0' && toupper(tb->buf[1]) == 'X') {
    fmt = "%llx";
    s   = tb->buf + 2;
  } else {
    fmt = "%lld";
    s   = tb->buf;
  }

  tokbuf_append_char(tb, 0);
  sscanf(s, fmt, &val);
  int_new(dst, val);
}

void
parse_str(inst_t *dst)
{
  struct tokbuf *tb = oolvm->inpfp->tb;
  
  str_newc(dst, 1, tb->len, tb->buf);
}

void
parse_quoted_str(inst_t *dst)
{
  struct tokbuf *tb = oolvm->inpfp->tb;

  char     *p = tb->buf + 1, c;
  unsigned n  = tb->len - 2;

  while (n > 0) {
    if (*p == '\\') {
      if (n <= 1) {
	parse_error("\\ with no following character\n");
      }
      switch (p[1]) {
      case 'n':
	c = '\n';
      replace1:
	*p = c;
	memmove(p + 1, p + 2, n - 2);
	--tb->len;
	++p;  n -= 2;
	continue;
      case 'r':
	c = '\r';
	goto replace1;
      case 't':
	c = '\t';
	goto replace1;
      case '\\':
	c = '\\';
	goto replace1;
      default:
	parse_error("Unrecognized \\ escape\n");
      }      
    }

    ++p;
    --n;
  }

  str_newc(dst, 1, tb->len - 1, tb->buf + 1);
}

void
parse_token(inst_t *dst)
{
  struct tokbuf *tb = oolvm->inpfp->tb;
  
  if (tb->len == 1) {
    switch (tb->buf[0]) {
    case '"':
      parse_quote(dst);
      return;

    case '(':
      parse_pair_or_list(dst);
      return;

    case '[':
      parse_method_call(dst);
      return;

    case '{':
      parse_block(dst);
      return;

    case ')':
    case ']':
    case '}':
      parse_error("Unbalanced %c\n", tb->buf[0]);

    default:
      ;
    }
  }

  if (tb->len >= 2 && tb->buf[0] == '`') {
    parse_quoted_str(dst);
    return;
  }

  if (tok_is_hex() || tok_is_int()) {
    parse_int(dst);
    return;
  }

  if (tok_is_float()) {
    parse_float(dst);
    return;
  }

  parse_str(dst);
}

bool
parse(inst_t *dst)
{
  if (!token_get())  return (false);

  parse_token(dst);

  return (true);
}


