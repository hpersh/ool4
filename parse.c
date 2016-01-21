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

void
stream_close(struct stream *str)
{
  (*str->funcs->close)(str);
}

bool
stream_file_eof(struct stream *str)
{
  return (feof(((struct stream_file *) str)->fp));
}

int
stream_file_getc(struct stream *str)
{
  return (fgetc(((struct stream_file *) str)->fp));
}

void
stream_file_ungetc(struct stream *str, char c)
{
  ungetc(c, ((struct stream_file *) str)->fp);
}

void
stream_file_close(struct stream *str)
{
  fclose(((struct stream_file *) str)->fp);
}

struct stream_funcs stream_funcs_file[] = {
  { .eof    = stream_file_eof,
    .getc   = stream_file_getc,
    .ungetc = stream_file_ungetc,
    .close  = stream_file_close,
  }
};

void
stream_file_init(struct stream_file *str, FILE *fp)
{
  str->base->funcs = stream_funcs_file;
  str->fp          = fp;
}

unsigned 
isspecial(unsigned c)
{
  switch (c) {
  case '\'':
  case '`':
  case ',':
  case '(':
  case ')':
  case '[':
  case ']':
  case '{':
  case '}':
    return (true);

  default:
    ;
  }

  return (false);
}

void
tokbuf_append_char(struct tokbuf *tb, char c)
{
  char     *p;
  unsigned n;

  if (tb->len >= tb->bufsize) {
    n = tb->bufsize << 1;
    p = mem_alloc(n, false);
    memcpy(p, tb->buf, tb->len);
    mem_free(tb->buf, tb->bufsize);
    
    tb->bufsize = n;
    tb->buf     = p;
  }
  
  tb->buf[tb->len++] = c;
}

unsigned
token_get(void)
{
  struct stream *str = FRAME_INPUT_PC->str;
  struct tokbuf *tb = FRAME_INPUT_PC->tb;
  unsigned result = false, eof = false;
  char     c;

  tb->len = 0;

  for (;;) {
    c = stream_getc(str);
    if (c < 0) {
      eof    = true;
      result = true;

      goto done;
    }
    if (!isspace(c))  break;
  }
  
  tokbuf_append_char(tb, c);

  if (c == '`') {
    unsigned depth = 1;
  
    for (;;) {
      c = stream_getc(str);
      if (c < 0)  goto done;
      
      if (c == '`')  ++depth;
      
      if (c == '\'')  --depth;
      
      tokbuf_append_char(tb, c);
      
      if (c == '\'' && depth == 0) {
	result = true;

	goto done;
      }
    }
  }

  if (isspecial(c)) {
    result = true;

    goto done;
  }

  for (;;) {
    c = stream_getc(str);
    if (c < 0 || isspace(c)) {
      result = true;

      goto done;
    }
    if (isspecial(c)) {
      stream_ungetc(str, c);

      result = true;

      goto done;
    }

    tokbuf_append_char(tb, c);
  }

 done:
  if (result) {
    if (!eof)  tokbuf_append_char(tb, 0);
  } else {
    tokbuf_fini(tb);
  }
  
  return (result);
}

unsigned parse_token(inst_t *dst);

unsigned
parse_quote(inst_t *dst)
{
  unsigned result;

  FRAME_WORK_BEGIN(1) {
    result = parse(&WORK(0));
    if (result) {
      list_new(&WORK(0), WORK(0), 0);
      
      method_call_new(&WORK(0), consts.str_quote, WORK(0));
      
      inst_assign(dst, WORK(0));
    }
  } FRAME_WORK_END;

  return (result);
}

unsigned
parse_pair_or_list(inst_t *dst)
{
  struct tokbuf *tb = FRAME_INPUT_PC->tb;
  unsigned result = false;
  unsigned pairf = false;

  FRAME_WORK_BEGIN(2) {
    unsigned i;
    inst_t   *p;
  
    for (i = 0, p = &WORK(0); ; ++i) {
      if (!token_get())  break;
      
      if (tb->len == 2) {
	switch (tb->buf[0]) {
	case ']':
	case '}':
	  goto done;
	case ',':
	  if (i != 1)  goto done;
	  pairf = true;
	  continue;
	case ')':
	  result = true;
	  goto done;
	}
      }
	
      if (pairf && i > 2
	  || !parse_token(&WORK(1))
	  ) {
	goto done;
      }
      
      list_new(p, WORK(1), 0);
      p = &CDR(*p);
    }

  done:
    if (result) {
      if (pairf) {
	pair_new(dst, CAR(WORK(0)), CAR(CDR(WORK(0))));
      } else {
	inst_assign(dst, WORK(0));
      }
    }
  } FRAME_WORK_END;

  return (result);
}

unsigned
parse_method_call(inst_t *dst)
{
  unsigned result = false;
  struct tokbuf *tb = FRAME_INPUT_PC->tb;

  FRAME_WORK_BEGIN(3) {
    unsigned i;
    inst_t    *p;

    for (i = 0, p = &WORK(1); ; ++i) {
      if (!token_get())  break;
      
      if (tb->len == 2) {
	if (tb->buf[0] == ']') {
	  result = true;
	  
	  break;
	}
	
	if (tb->buf[0] == ')' || tb->buf[0] =='}') {
	  break;
	}
      }
      
      if (!parse_token(&WORK(2)))  break;
      
      if (i & 1) {
	if (inst_of(WORK(2)) != consts.cl_str)  break;
	
	if (i == 1) {
	  inst_assign(&WORK(0), WORK(2));
	} else {
	  str_newc(&WORK(0), 2, STRVAL(WORK(0))->size, STRVAL(WORK(0))->data,
		                STRVAL(WORK(2))->size, STRVAL(WORK(2))->data
		   );
	}
	
	continue;
      }
      
      list_new(p, WORK(2), 0);
      p = &CDR(*p);
    }

    if (result)  method_call_new(dst, WORK(0), WORK(1));
  } FRAME_WORK_END;

  return (result);
}

unsigned
parse_block(inst_t *dst)
{
  unsigned result = false;
  struct tokbuf *tb = FRAME_INPUT_PC->tb;

  FRAME_WORK_BEGIN(3) {
    unsigned i;
    inst_t    *p;

    for (i = 0, p = &WORK(1); ; ++i) {
      if (!token_get())  break;
      
      if (tb->len == 2){
	if (tb->buf[0] == '}') {
	  result = true;
	  
	  break;
	}
	
	if (tb->buf[0] == ')' || tb->buf[0] == ']') {
	  break;
	}
      }
      
      if (!parse_token(&WORK(2)))  break;
      
      if (i == 0) {
	if (!(WORK(2) == 0 || inst_of(WORK(2)) == consts.cl_list))  break;
	
	inst_assign(&WORK(0), WORK(2));
	
	continue;
      }
      
      list_new(p, WORK(2), 0);
      p = &CDR(*p);
    }
    
    if (result)  block_new(dst, WORK(0), WORK(1));
  } FRAME_WORK_END;

  return (result);
}

unsigned
parse_dot(inst_t *dst)
{
  unsigned result;

  FRAME_WORK_BEGIN(1) {
    result = parse(&WORK(0));
    if (result) {
      list_new(&WORK(0), WORK(0), 0);
      method_call_new(&WORK(0), consts.str_quote, WORK(0));
      
      list_new(&WORK(0), WORK(0), 0);
      list_new(&WORK(0), *dst, WORK(0));
      method_call_new(&WORK(0), consts.str_atc, WORK(0));
      
      inst_assign(dst, WORK(0));
    }
  } FRAME_WORK_END;

  return (result);
}

unsigned
parse_str(inst_t *dst)
{
  struct tokbuf *tb = FRAME_INPUT_PC->tb;
  
  FRAME_WORK_BEGIN(2) {
    char     *p, *q;
    unsigned i, n, k;

    for (i = 0, p = tb->buf, n = tb->len; n > 0; n -= k, p += k, ++i) {
      q = index(p, '.');
      if (q == 0) {
	k = n;
      } else {
	k = q + 1 - p;
	*q = 0;
      }
      
      str_newc(&WORK(1), 1, k, p);
      
      if (i == 0) {
	inst_assign(&WORK(0), WORK(1));
      } else {
	list_new(&WORK(1), WORK(1), 0);
	method_call_new(&WORK(1), consts.str_quote, WORK(1));
	
	list_new(&WORK(1), WORK(1), 0);
	list_new(&WORK(1), WORK(0), WORK(1));
	method_call_new(&WORK(0), consts.str_atc, WORK(1));
      }
    }
    
    inst_assign(dst, WORK(0));
  } FRAME_WORK_END;

  return (true);
}

unsigned
parse_token(inst_t *dst)
{
  unsigned result;
  struct tokbuf *tb = FRAME_INPUT_PC->tb;
  char     *p;
  unsigned n, negf;
  
  if (tb->len == 2) {
    switch (tb->buf[0]) {
    case '\'':
      return (parse_quote(dst));

    case '(':
      return (parse_pair_or_list(dst));

    case '[':
      return (parse_method_call(dst));

    case '{':
      return (parse_block(dst));

    default:
      ;
    }
  }

  if (tb->len >= 2 && tb->buf[0] == '`') {
    FRAME_WORK_BEGIN(1) {
      tb->buf[tb->len - 2] = 0;
      str_newc(&WORK(0), 1, tb->len - 2, tb->buf + 1);
      
      list_new(&WORK(0), WORK(0), 0);
      
      method_call_new(&WORK(0), consts.str_quote, WORK(0));
      
      inst_assign(dst, WORK(0));
    } FRAME_WORK_END;

    return (true);
  }

  p = tb->buf;
  n = tb->len;

  negf = false;
  if (*p == '-') {
    negf = true;
    
    ++p;
    --n;
  }

  for ( ; n > 1 && *p >= '0' && *p <= '9'; --n, ++p);
  
  if (n > 1) {
    parse_str(dst);
  } else {
    intval_t val;
    
    sscanf(tb->buf, "%lld", &val);

    int_new(dst, val);
  }

  return (true);
}

unsigned
parse(inst_t *dst)
{
  unsigned result;

  result = token_get();
  
  if (result) {
    if (FRAME_INPUT_PC->tb->len == 0)  return (PARSE_EOF);

    result = parse_token(dst);
  }

  return (result ? PARSE_OK : PARSE_ERR);
}


