#include <stdarg.h>
#include <string.h>
#include <setjmp.h>
#include <stdio.h>

#define ARRAY_SIZE(a)  (sizeof(a) / sizeof((a)[0]))

#define PTR_TO_UINT(x)  ((unsigned long long)(x))
#define FIELD_OFS(s, f)  PTR_TO_UINT(&((s *) 0)->f)
#define FIELD_PTR_TO_STRUCT_PTR(p, s, f)  ((s *)((char *)(p) - FIELD_OFS(s, f)))

enum {
  false = 0, true
};
typedef unsigned char bool;

struct list {
  struct list *prev, *next;
};

static inline void
list_init(struct list *li)
{
  li->prev = li->next = li;
}

static inline bool
list_empty(struct list *li)
{
  return (li->next == li);
}

static inline struct list *
list_first(struct list *li)
{
  return(li->next);
}

static inline struct list *
list_last(struct list *li)
{
  return(li->prev);
}

static inline struct list *
list_end(struct list *li)
{
  return(li);
}

static inline struct list *
list_prev(struct list *item)
{
  return(item->prev);
}

static inline struct list *
list_next(struct list *item)
{
  return(item->next);
}

struct list *list_insert(struct list *item, struct list *before);
void        list_erase(struct list *item);

enum {
  MIN_BLK_SIZE_LOG2  = 4,
  MIN_BLK_SIZE       = 1 << MIN_BLK_SIZE_LOG2
};

void *mem_alloc(unsigned size, bool clr);
void mem_free(void *p, unsigned size);

struct inst;
typedef struct inst *inst_t;

struct inst {
  struct list list_node[1];
  unsigned    ref_cnt;
  inst_t      inst_of;
};

struct inst_bool {
  struct inst base[1];
  bool        val;
};
#define BOOLVAL(x)  (((struct inst_bool *)(x))->val)
void bool_new(inst_t *dst, bool val);

typedef long long intval_t;

struct inst_int {
  struct inst base[1];
  intval_t    val;
};
#define INTVAL(x)  (((struct inst_int *)(x))->val)
void int_new(inst_t *dst, intval_t val);

typedef long double floatval_t;

struct inst_float {
  struct inst base[1];
  floatval_t  val;
};
#define FLOATVAL(x)  (((struct inst_float *)(x))->val)
void float_new(inst_t *dst, floatval_t val);

struct inst_code_method {
  struct inst base[1];
  void        (*val)(void);
};
#define CODEMETHODVAL(x)  (((struct inst_code_method *)(x))->val)
void code_method_new(inst_t *dst, void (*func)(void));

struct inst_str {
  struct inst base[1];
  struct {
    unsigned size;
    char     *data;
  } val[1];
};
#define STRVAL(x)  (((struct inst_str *)(x))->val)
void str_newc(inst_t *dst, unsigned argc, ...);
void str_newv(inst_t *dst, unsigned n, inst_t *data);

struct inst_dptr {
  struct inst base[1];
  struct {
    inst_t car, cdr;
  } val[1];
};
#define CAR(x)  (((struct inst_dptr *)(x))->val->car)
#define CDR(x)  (((struct inst_dptr *)(x))->val->cdr)
void pair_new(inst_t *dst, inst_t car, inst_t cdr);
void list_new(inst_t *dst, inst_t car, inst_t cdr);
unsigned list_len(inst_t li);

struct inst_dptr_cnt {
  struct inst_dptr base[1];
  struct {
    unsigned cnt;
  } val[1];
};
#define DPTRCNTVAL(x)  (((struct inst_dptr_cnt *)(x))->val)
void method_call_new(inst_t *dst, inst_t sel, inst_t args);
void block_new(inst_t *dst, inst_t args, inst_t body);

struct inst_array {
  struct inst base[1];
  struct {
    unsigned size;
    inst_t   *data;
  } val[1];
};
#define ARRAYVAL(x)  (((struct inst_array *)(x))->val)
void array_new(inst_t *dst, unsigned size);

struct inst_set {
  struct inst_array base[1];
  struct {
    inst_t   *(*find)(inst_t, inst_t, inst_t **);
    unsigned cnt;
  } val[1];
};
#define SETVAL(x)  (((struct inst_set *)(x))->val)
void set_new(inst_t *dst, unsigned size);
void strdict_new(inst_t *dst, unsigned size);
void dict_new(inst_t *dst, unsigned size);
inst_t dict_at(inst_t dict, inst_t key);
void   dict_at_put(inst_t dict, inst_t key, inst_t val);
void   dict_keys(inst_t *dst, inst_t dict);

struct inst_file {
  struct inst base[1];
  struct {
    FILE *fp;
  } val[1];
};
#define FILEVAL(x) (((struct inst_file *)(x))->val)
void file_new(inst_t *dst, FILE *fp);

struct inst_module {
  struct inst_set base[1];
  struct {
    inst_t name;
  } val[1];
};
#define MODULEVAL(x)  (((struct inst_module *)(x))->val)
void module_new(inst_t *dst, inst_t name);

struct inst_metaclass {
  struct inst base[1];
  struct {
    inst_t name, module, parent;
    inst_t cl_vars, cl_methods, inst_vars, inst_methods;
    unsigned inst_size;
    void (*init)(inst_t inst, inst_t cl, unsigned argc, va_list ap);
    void (*walk)(inst_t inst, inst_t cl, void (*func)(inst_t));
    void (*free)(inst_t inst, inst_t cl);
  } val[1];
};
#define CLASSVAL(x)  (((struct inst_metaclass *)(x))->val)
#define CLASSVAL_OFS(x)  (FIELD_OFS(struct inst_metaclass, val-> x))

struct {
  inst_t metaclass;
  inst_t module_main;

  inst_t cl_object;
  inst_t cl_bool;
  inst_t cl_int;
  inst_t cl_code_method;
  inst_t cl_str;
  inst_t cl_dptr;
  inst_t cl_pair;
  inst_t cl_list;
  inst_t cl_method_call;
  inst_t cl_block;
  inst_t cl_array;
  inst_t cl_dict;
  inst_t cl_file;
  inst_t cl_module;
  inst_t cl_env;
  inst_t cl_system;
  
  inst_t str_addc;
  inst_t str_andc;
  inst_t str_atc;
  inst_t str_atc_defc;
  inst_t str_atc_lengthc;
  inst_t str_atc_putc;
  inst_t str_array;
  inst_t str_boolean;
  inst_t str_block;
  inst_t str_car;
  inst_t str_cdr;
  inst_t str_class_methods;
  inst_t str_class_variables;
  inst_t str_code_method;
  inst_t str_delc;
  inst_t str_dictionary;
  inst_t str_dptr;
  inst_t str_environment;
  inst_t str_equalc;
  inst_t str_eval;
  inst_t str_evalc;
  inst_t str_false;
  inst_t str_file;
  inst_t str_hash;
  inst_t str_instance_methods;
  inst_t str_instance_variables;
  inst_t str_integer; 
  inst_t str_keys;
  inst_t str_list;
  inst_t str_load;
  inst_t str_ltc;
  inst_t str_main;
  inst_t str_metaclass;
  inst_t str_method_call;
  inst_t str_module;
  inst_t str_object;
  inst_t str_new;
  inst_t str_newc;
  inst_t str_newc_modec;
  inst_t str_newc_parentc_instancevariablesc;
  inst_t str_pair;
  inst_t str_quote;
  inst_t str_string;
  inst_t str_system;
  inst_t str_tostring;
  inst_t str_true;
  inst_t str_whilec;
  inst_t str__write;
  inst_t str_write;
  inst_t str_writec;
} consts;

inst_t inst_retain(inst_t inst);
void   inst_release(inst_t inst);

static inline inst_t
inst_of(inst_t inst)
{
  return (inst == 0 ? consts.cl_object : inst->inst_of);
}

unsigned is_subclass_of(inst_t cl1, inst_t cl2);
unsigned is_kind_of(inst_t inst, inst_t cl);

static inline bool
is_list(inst_t inst)
{
  return (inst == 0 || inst_of(inst) == consts.cl_list);
}

static inline void
inst_assign(inst_t *dst, inst_t src)
{
  inst_t temp = *dst;

  *dst = inst_retain(src);
  inst_release(temp);
}

struct stream;

struct stream_funcs {
  bool (*eof)(struct stream *);
  int  (*getc)(struct stream *);
  void (*ungetc)(struct stream *, char c);
};

struct stream {
  struct stream_funcs *funcs;
};

struct stream_file {
  struct stream base[1];
  
  FILE *fp;
};

struct stream_buf {
  struct stream base[1];
  
  char     *buf;
  unsigned len, ofs;
};

void stream_file_init(struct stream_file *str, FILE *fp);
void stream_buf_init(struct stream_buf *str, char *buf, unsigned len);

bool stream_eof(struct stream *str);
int  stream_getc(struct stream *str);
void stream_ungetc(struct stream *str, char c);
void stream_close(struct stream *str);

struct tokbuf {
  unsigned bufsize;
  unsigned len ;
  char     *buf;
};

static inline void
tokbuf_init(struct tokbuf *tb)
{
  tb->buf = (char *) mem_alloc(tb->bufsize = MIN_BLK_SIZE, false);
  tb->len = 0;
}

static inline void
tokbuf_fini(struct tokbuf *tb)
{
  if (tb->buf != 0)  mem_free(tb->buf, tb->bufsize);
}

struct parse_ctxt {
  struct stream *str;
  struct tokbuf tb[1];
};

static void inline
parse_ctxt_init(struct parse_ctxt *pc, struct stream *str)
{
  pc->str = str;
  tokbuf_init(pc->tb);
}

static inline void
parse_ctxt_fini(struct parse_ctxt *pc)
{
  tokbuf_fini(pc->tb);
}

enum {
  PARSE_EOF, PARSE_OK, PARSE_ERR
};

unsigned parse(inst_t *dst);

enum {
  FRAME_TYPE_WORK,
  FRAME_TYPE_METHOD_CALL,
  FRAME_TYPE_MODULE,
  FRAME_TYPE_ERROR,
  FRAME_TYPE_BLOCK,
  FRAME_TYPE_INPUT,
};

struct frame {
  struct frame *prev;
  unsigned     type;
};

struct frame *fp;

static inline void
frame_push(struct frame *fr, unsigned type)
{
  fr->prev = fp;
  fr->type = type;

  fp = fr;
}

static inline void
frame_pop(void)
{
  fp = fp->prev;
}

struct frame_work {
  struct frame      base[1];
  struct frame_work *prev;
  unsigned          size;
  inst_t            *data;
};

struct frame_work *wfp;

static inline void
frame_work_push(struct frame_work *fr, unsigned size, inst_t *data)
{
  frame_push(fr->base, FRAME_TYPE_WORK);

  fr->prev = wfp;
  memset(fr->data = data, 0, (fr->size = size) * sizeof(fr->data[0]));

  wfp = fr;
}

static inline void
frame_work_pop(void)
{
  inst_t   *p;
  unsigned n;
  
  for (p = wfp->data, n = wfp->size; n > 0; --n, ++p)  inst_release(*p);

  wfp = wfp->prev;
  frame_pop();
}

#define FRAME_WORK_BEGIN(n)				\
  {							\
    inst_t __frame_work_data[n];			\
    struct frame_work __frame_work[1];			\
    frame_work_push(__frame_work, (n), __frame_work_data);

#define WORK(i)  (__frame_work_data[i])

#define FRAME_WORK_END	 \
    frame_work_pop();    \
  }

struct frame_method_call {
  struct frame base[1];
  struct frame_method_call *prev;
  inst_t       *result, cl, sel, *argv;
  unsigned     argc;
};

struct frame_method_call *mcfp;

static inline void
frame_method_call_push(struct frame_method_call *fr, inst_t *result, inst_t cl, inst_t sel, unsigned argc, inst_t *argv)
{
  frame_push(fr->base, FRAME_TYPE_METHOD_CALL);

  fr->prev   = mcfp;
  fr->result = result;
  fr->cl     = cl;
  fr->sel    = sel;
  fr->argc   = argc;
  fr->argv   = argv;

  mcfp = fr;
}

static inline void
frame_method_call_pop(void)
{
  mcfp = mcfp->prev;
  frame_pop();
}

#define FRAME_METHOD_CALL_BEGIN(_rslt, _cl, _sel, _argc, _argv)		\
  {									\
    struct frame_method_call __fr[1];					\
    frame_method_call_push(__fr, (_rslt), (_cl), (_sel), (_argc), (_argv));

#define MC_RESULT  (mcfp->result)
#define MC_ARGC    (mcfp->argc)
#define MC_ARG(i)  (mcfp->argv[i])
#define MC_SEL     (mcfp->sel)

#define FRAME_METHOD_CALL_END	\
    frame_method_call_pop();    \
  }

struct frame_module {
  struct frame        base[1];
  struct frame_module *prev;
  inst_t              cur;	/* Current, for adding */
  inst_t              ctxt;	/* Search context */
};

struct frame_module *modfp;

static inline void
frame_module_push(struct frame_module *fr, inst_t cur, inst_t ctxt)
{
  frame_push(fr->base, FRAME_TYPE_MODULE);

  fr->prev = modfp;
  fr->cur  = cur;
  fr->ctxt = ctxt;

  modfp = fr;
}

static inline void
frame_module_pop(void)
{
  modfp = modfp->prev;

  frame_pop();
}

#define FRAME_MODULE_BEGIN(_cur, _ctxt)		\
  {						\
    struct frame_module __fr[1];		\
    frame_module_push(__fr, (_cur), (_ctxt));

#define MODULE_CUR   (modfp->cur)
#define MODULE_CTXT  (modfp->cur)

#define FRAME_MODULE_END \
    frame_module_pop();	 \
  }

struct frame_jmp {
  struct frame base[1];
  jmp_buf      jmp_buf;
  int          code;
};

void frame_jmp(struct frame_jmp *fr, int code);

struct frame_error {
  struct frame_jmp   base[1];
  struct frame_error *prev;
};

struct frame_error *errfp;

static inline void
frame_error_push(struct frame_error *fr)
{
  frame_push(fr->base->base, FRAME_TYPE_ERROR);
  fr->prev = errfp;
  errfp = fr;
}

static inline void
frame_error_pop(void)
{
  errfp = errfp->prev;
  frame_pop();
}

#define FRAME_ERROR_BEGIN					\
  {								\
    struct frame_error __frame_error[1];			\
    frame_error_push(__frame_error);				\
    __frame_error->base->code = setjmp(__frame_error->base->jmp_buf);

#define FRAME_ERROR_CODE (__frame_error->base->code)

#define FRAME_ERROR_END	  \
    frame_error_pop();	  \
  }

struct frame_block {
  struct frame_jmp   base[1];
  struct frame_block *prev;
  inst_t             dict;
};

struct frame_block *blkfp;

static inline void
frame_block_push(struct frame_block *fr, inst_t dict)
{
  frame_push(fr->base->base, FRAME_TYPE_BLOCK);
  fr->prev = blkfp;
  fr->dict = dict;
  blkfp = fr;
}

static inline void
frame_block_pop(void)
{
  blkfp = blkfp->prev;
  frame_pop();
}

#define FRAME_BLOCK_BEGIN(dict)						\
  {									\
    struct frame_block __frame_block[1];				\
    frame_block_push(__frame_block, (dict));				\
    __frame_block->base->code = setjmp(__frame_block->base->jmp_buf);

#define FRAME_BLOCK_END \
    frame_block_pop();	\
  }

struct frame_input {
  struct frame_jmp   base[1];
  struct frame_input *prev;
  struct parse_ctxt  pc[1];
};

struct frame_input *inpfp;

static inline void
frame_input_push(struct frame_input *fr, struct stream *str)
{
  frame_push(fr->base->base, FRAME_TYPE_INPUT);

  parse_ctxt_init(fr->pc, str);

  fr->prev = inpfp;
  inpfp = fr;
}

static inline void
frame_input_pop(void)
{
  parse_ctxt_fini(inpfp->pc);

  inpfp = inpfp->prev;
  frame_pop();
}

#define FRAME_INPUT_BEGIN(_str)				\
  {							\
    struct frame_input __frame_input[1];		\
    frame_input_push(__frame_input, (_str));		\
    parse_ctxt_init(__frame_input->pc, (_str));

#define FRAME_INPUT_PC   (inpfp->pc)

#define FRAME_INPUT_END \
    frame_input_pop();	\
  }

void error(char *msg);
