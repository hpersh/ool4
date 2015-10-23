#include <stdio.h>
#include <ctype.h>

#include "ool.h"


int
stream_getc(struct stream *str)
{
  return ((*str->funcs->getc)(str));
}

void
stream_ungetc(struct stream *str, char c)
{
  return ((*str->funcs->ungetc)(str, c));
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

struct stream_funcs stream_funcs_file[] = {
  { .getc   = stream_file_getc,
    .ungetc = stream_file_ungetc
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
tokbuf_fini(struct tokbuf *tb)
{
  if (tb->bufsize > 0)  mem_free(tb->buf, tb->bufsize);
}

void
tokbuf_init(struct tokbuf *tb)
{
  memset(tb, 0, sizeof(*tb));
}

void
tokbuf_append_char(struct tokbuf *tb, char c)
{
  char     *p;
  unsigned n;

  if (tb->len < ARRAY_SIZE(tb->data)) {
    p = tb->data;
  } else {
    if (tb->len >= tb->bufsize) {
      n = (tb->bufsize == 0 ? ARRAY_SIZE(tb->data) : tb->bufsize) << 1;
      p = mem_alloc(n);
      if (tb->bufsize == 0) {
	memcpy(p, tb->data, tb->len);
      } else {
	memcpy(p, tb->buf, tb->len);
	mem_free(tb->buf, tb->bufsize);
      }
      
      tb->bufsize = n;
      tb->buf     = p;
    }

    p = tb->buf;
  }

  p[tb->len] = c;
  ++tb->len;
}

char *
tokbuf_data(struct tokbuf *tb)
{
  return (tb->bufsize > 0 ? tb->buf : tb->data);
}

unsigned
tokbuf_len(struct tokbuf *tb)
{
  return (tb->len);
}

unsigned
token_get(struct stream *str, struct tokbuf *tb)
{
  unsigned result = false, eof = false;
  char     c;

  tokbuf_fini(tb);
  tokbuf_init(tb);

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



unsigned parse_token(inst_t *dst, struct stream *str, char *buf, unsigned len);

unsigned
parse_quote(inst_t *dst, struct stream *str)
{
  unsigned result;

  FRAME_WORK_BEGIN(1) {
    struct parse_ctxt pc[1];

    parse_ctxt_init(pc, str);

    result = parse(&WORK(0), pc);
    if (result) {
      list_new(&WORK(0), WORK(0), 0);
      
      method_call_new(&WORK(0), consts.str_quote, WORK(0));
      
      inst_assign(dst, WORK(0));
    }
    
    parse_ctxt_fini(pc);
  } FRAME_WORK_END;

  return (result);
}

unsigned
parse_pair_or_list(inst_t *dst, struct stream *str)
{
  unsigned result = false;
  unsigned pairf = false;

  FRAME_WORK_BEGIN(2) {
    struct parse_ctxt pc[1];

    parse_ctxt_init(pc, str);
    
    unsigned i;
    inst_t   *p;
  
    for (i = 0, p = &WORK(0); ; ++i) {
      if (!token_get(str, pc->tb))  break;
      
      char *t    = tokbuf_data(pc->tb);
      unsigned n = tokbuf_len(pc->tb);
      
      if (n == 2 && t[0] == ',') {
	if (i != 1)  break;
	
	pairf = true;
	
	continue;
      }
      
      if (n == 2) {
	if (t[0] == ')') {
	  result = true;
	  
	  break;
	}
	
	if (t[0] == ']' || t[0] =='}') {
	  break;
	}
	
      }
      
      if (pairf && i > 2)  break;
      
      if (!parse_token(&WORK(1), str, t, n))  break;
      
      if (pairf) {
	pair_new(&WORK(0), CAR(WORK(0)), WORK(1));
      } else {
	list_new(p, WORK(1), 0);
	p = &CDR(*p);
      }
    }
    
    parse_ctxt_fini(pc);
    
    if (result)  inst_assign(dst, WORK(0));
  } FRAME_WORK_END;

  return (result);
}

unsigned
parse_method_call(inst_t *dst, struct stream *str)
{
  unsigned result = false;

  FRAME_WORK_BEGIN(3) {
    struct parse_ctxt pc[1];

    parse_ctxt_init(pc, str);

    unsigned i;
    inst_t    *p;

    for (i = 0, p = &WORK(1); ; ++i) {
      if (!token_get(str, pc->tb))  break;
      
      char *t = tokbuf_data(pc->tb);
      unsigned n = tokbuf_len(pc->tb);

      if (n == 2) {
	if (t[0] == ']') {
	  result = true;
	  
	  break;
	}
	
	if (t[0] == ')' || t[0] =='}') {
	  break;
	}
      }
      
      if (!parse_token(&WORK(2), str, t, n))  break;
      
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

    parse_ctxt_fini(pc);
  
    if (result)  method_call_new(dst, WORK(0), WORK(1));
  } FRAME_WORK_END;

  return (result);
}

unsigned
parse_block(inst_t *dst, struct stream *str)
{
  unsigned result = false;

  FRAME_WORK_BEGIN(3) {
    struct parse_ctxt pc[1];

    parse_ctxt_init(pc, str);
    
    unsigned i;
    inst_t    *p;

    for (i = 0, p = &WORK(1); ; ++i) {
      if (!token_get(str, pc->tb))  break;
      
      char *t = tokbuf_data(pc->tb);
      unsigned n = tokbuf_len(pc->tb);
      
      if (n == 2){
	if (t[0] == '}') {
	  result = true;
	  
	  break;
	}
	
	if (t[0] == ')' || t[0] == ']') {
	  break;
	}
      }
      
      if (!parse_token(&WORK(2), str, t, n))  break;
      
      if (i == 0) {
	if (!(WORK(2) == 0 || inst_of(WORK(2)) == consts.cl_list))  break;
	
	inst_assign(&WORK(0), WORK(2));
	
	continue;
      }
      
      list_new(p, WORK(2), 0);
      p = &CDR(*p);
    }
    
    parse_ctxt_fini(pc);
    
    if (result)  block_new(dst, WORK(0), WORK(1));
  } FRAME_WORK_END;

  return (result);
}

unsigned
parse_dot(inst_t *dst, struct stream *str)
{
  unsigned result;

  FRAME_WORK_BEGIN(1) {
    struct parse_ctxt pc[1];
    
    parse_ctxt_init(pc, str);
    
    result = parse(&WORK(0), pc);
    if (result) {
      list_new(&WORK(0), WORK(0), 0);
      method_call_new(&WORK(0), consts.str_quote, WORK(0));
      
      list_new(&WORK(0), WORK(0), 0);
      list_new(&WORK(0), *dst, WORK(0));
      method_call_new(&WORK(0), consts.str_atc, WORK(0));
      
      inst_assign(dst, WORK(0));
    }
    
    parse_ctxt_fini(pc);
  } FRAME_WORK_END;

  return (result);
}

unsigned
parse_str(inst_t *dst, char *buf, unsigned len)
{
  FRAME_WORK_BEGIN(2) {
    unsigned i, n;

    for (i = 0; len > 0; len -= n, buf += n, ++i) {
      char *p = index(buf, '.');
      if (p == 0) {
	n = len;
      } else {
	n = p + 1 - buf;
	*p = 0;
      }
      
      str_newc(&WORK(1), 1, n, buf);
      
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
parse_token(inst_t *dst, struct stream *str, char *buf, unsigned len)
{
  unsigned result;
  char     *p;
  unsigned n, negf;
  
  if (len == 2) {
    switch (buf[0]) {
    case '\'':
      return (parse_quote(dst, str));

    case '(':
      return (parse_pair_or_list(dst, str));

    case '[':
      return (parse_method_call(dst, str));

    case '{':
      return (parse_block(dst, str));

    default:
      ;
    }
  }

  if (len >= 2 && buf[0] == '`') {
    FRAME_WORK_BEGIN(1) {
      buf[len - 2] = 0;
      str_newc(&WORK(0), 1, len - 2, buf + 1);
      
      list_new(&WORK(0), WORK(0), 0);
      
      method_call_new(&WORK(0), consts.str_quote, WORK(0));
      
      inst_assign(dst, WORK(0));
    } FRAME_WORK_END;

    return (true);
  }

  p = buf;
  n = len;

  negf = false;
  if (*p == '-') {
    negf = true;
    
    ++p;
    --n;
  }

  for ( ; n > 1 && *p >= '0' && *p <= '9'; --n, ++p);
  
  if (n > 1) {
    parse_str(dst, buf, len);
  } else {
    intval_t val;
    
    sscanf(buf, "%lld", &val);

    int_new(dst, val);
  }

  return (true);
}


void
parse_ctxt_init(struct parse_ctxt *pc, struct stream *str)
{
  pc->str = str;

  tokbuf_init(pc->tb);
}

void
parse_ctxt_fini(struct parse_ctxt *pc)
{
  tokbuf_fini(pc->tb);
}

unsigned
parse(inst_t *dst, struct parse_ctxt *pc)
{
  unsigned result;

  result = token_get(pc->str, pc->tb);
  
  if (result) {
    if (tokbuf_len(pc->tb) == 0)  return (PARSE_EOF);

    result = parse_token(dst, pc->str, tokbuf_data(pc->tb), tokbuf_len(pc->tb));
  }

  return (result ? PARSE_OK : PARSE_ERR);
}


