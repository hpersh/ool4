#include <stdarg.h>
#include <string.h>
#include <setjmp.h>
#include <stdio.h>
#include <assert.h>

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
  return (li->next);
}

static inline struct list *
list_last(struct list *li)
{
  return (li->prev);
}

static inline struct list *
list_end(struct list *li)
{
  return (li);
}

static inline struct list *
list_prev(struct list *item)
{
  return (item->prev);
}

static inline struct list *
list_next(struct list *item)
{
  return (item->next);
}

struct list *list_insert(struct list *item, struct list *before);
void        list_erase(struct list *item);

enum { CLIST_DATA_SIZE = 512 };

struct clist {
  struct clist *next;
  char         data[CLIST_DATA_SIZE];
};

enum {
  MIN_BLK_SIZE_LOG2  = 4,
  MIN_BLK_SIZE       = 1 << MIN_BLK_SIZE_LOG2
};

void *mem_alloc(unsigned size, bool clr);
void mem_free(void *p, unsigned size);
void *mem_frame_alloc(unsigned size);
void mem_frame_free(unsigned size);

struct inst;
typedef struct inst *inst_t;

struct inst {
  struct list list_node[1];
  unsigned    ref_cnt;
#ifndef NDEBUG
  unsigned    old_ref_cnt;
#endif
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
  struct {
    inst_t module;
    void   (*func)(void);
  } val[1];
};
#define CODEMETHODVAL(x)  (((struct inst_code_method *)(x))->val)
void code_method_new(inst_t *dst, inst_t module, void (*func)(void));

struct inst_str {
  struct inst base[1];
  struct {
    unsigned size;
    char     *data;
  } val[1];
};
#define STRVAL(x)  (((struct inst_str *)(x))->val)
void str_alloc(inst_t *dst, unsigned size);
void str_newc(inst_t *dst, unsigned argc, ...);
void str_newv(inst_t *dst, unsigned n, inst_t *data);
void str_newcl(inst_t *dst, unsigned size, struct clist *cl);

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

struct inst_barray {
  struct inst base[1];
  struct {
    unsigned      size;
    unsigned char *data;
  } val[1];
};
#define BARRAYVAL(x)  (((struct inst_barray *)(x))->val)
void barray_new(inst_t *dat, unsigned size);
void barray_copy(inst_t *dst, inst_t src, unsigned ofs, unsigned len);

struct inst_array {
  struct inst base[1];
  struct {
    unsigned size;
    inst_t   *data;
  } val[1];
};
#define ARRAYVAL(x)  (((struct inst_array *)(x))->val)
void array_new(inst_t *dst, unsigned size);
void array_copy(inst_t *dst, inst_t *src, unsigned size);

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
    inst_t filename;
    inst_t mode;
    FILE *fp;
  } val[1];
};
#define FILEVAL(x) (((struct inst_file *)(x))->val)
void file_new(inst_t *dst, inst_t filename, inst_t mode, FILE *fp);

struct inst_module {
  struct inst_set base[1];
  struct {
    inst_t name;
    inst_t filename;
    inst_t sha1;
    void   *dl;
  } val[1];
};
#define MODULEVAL(x)  (((struct inst_module *)(x))->val)
void module_new(inst_t *dst, inst_t name, inst_t filename, inst_t sha1);

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
  inst_t cl_float;
  inst_t cl_code_method;
  inst_t cl_str;
  inst_t cl_dptr;
  inst_t cl_pair;
  inst_t cl_list;
  inst_t cl_method_call;
  inst_t cl_block;
  inst_t cl_barray;
  inst_t cl_array;
  inst_t cl_dict;
  inst_t cl_file;
  inst_t cl_module;
  inst_t cl_except;
  inst_t cl_env;
  inst_t cl_system;
  
  inst_t str___ool_exception_cannot_instantiate;
  inst_t str___ool_exception_argument_count;
  inst_t str_addc;
  inst_t str_aandc;
  inst_t str_andc;
  inst_t str_asc;
  inst_t str_atc;
  inst_t str_atc_defc;
  inst_t str_atc_lengthc;
  inst_t str_atc_putc;
  inst_t str_array;
  inst_t str_boolean;
  inst_t str_block;
  inst_t str_byte_array;
  inst_t str_car;
  inst_t str_cdr;
  inst_t str_chr;
  inst_t str_class_methods;
  inst_t str_class_variables;
  inst_t str_code_method;
  inst_t str_cond;
  inst_t str_delc;
  inst_t str_dictionary;
  inst_t str_dptr;
  inst_t str_environment;
  inst_t str_equalc;
  inst_t str_eval;
  inst_t str_evalc;
  inst_t str_exception;
  inst_t str_exit;
  inst_t str_exitc;
  inst_t str_false;
  inst_t str_file;
  inst_t str_filename;
  inst_t str_gtc;
  inst_t str_float;
  inst_t str_hash;
  inst_t str_hex;
  inst_t str_imatchc;
  inst_t str_instance_methods;
  inst_t str_instance_of;
  inst_t str_instance_variables;
  inst_t str_integer; 
  inst_t str_joinc;
  inst_t str_keys;
  inst_t str_list;
  inst_t str_load;
  inst_t str_ltc;
  inst_t str_main;
  inst_t str_matchc;
  inst_t str_metaclass;
  inst_t str_method_call;
  inst_t str_module;
  inst_t str_multc;
  inst_t str_object;
  inst_t str_name;
  inst_t str_new;
  inst_t str_newc;
  inst_t str_newc_modec;
  inst_t str_newc_parentc_instancevariablesc;
  inst_t str_not;
  inst_t str_pair;
  inst_t str_prog;
  inst_t str_quote;
  inst_t str_raisec;
  inst_t str_read;
  inst_t str_readc;
  inst_t str_readln;
  inst_t str_sha1;
  inst_t str_size;
  inst_t str_string;
  inst_t str_system;
  inst_t str_tostring;
  inst_t str_toupper;
  inst_t str_true;
  inst_t str_tryc_catchc_finallyc;
  inst_t str_whilec;
  inst_t str__write;
  inst_t str_write;
  inst_t str_writec;
} consts;

void inst_init_parent(inst_t inst, inst_t cl, unsigned argc, va_list ap);
void inst_walk_parent(inst_t inst, inst_t cl, void (*func)(inst_t));
void inst_free_parent(inst_t inst, inst_t cl);

void   inst_alloc(inst_t *dst, inst_t cl);
void   inst_init(inst_t inst, unsigned argc, ...);
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
  
  FILE     *fp;
  char     last;
  unsigned line;
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

void tokbuf_append(struct tokbuf *tb, unsigned n, char *s);
void tokbuf_append_char(struct tokbuf *tb, char c);

bool parse(inst_t *dst);

enum {
  FRAME_TYPE_SCRATCH = 0xaa55ff01,
  FRAME_TYPE_WORK,
  FRAME_TYPE_METHOD_CALL,
  FRAME_TYPE_MODULE,
  FRAME_TYPE_BLOCK,
  FRAME_TYPE_INPUT,
  FRAME_TYPE_EXCEPT
};

struct frame {
  struct frame *prev;
  unsigned     type;
};

struct frame_scratch {
  struct frame  base[1];
  unsigned      size;
  unsigned char data[0];
};

struct frame_work {
  struct frame      base[1];
  struct frame_work *prev;
  unsigned          size;
  inst_t            data[0];
};

struct frame_method_call {
  struct frame base[1];
  struct frame_method_call *prev;
  inst_t       *result, cl, sel, *argv;
  unsigned     argc;
};

struct frame_module {
  struct frame        base[1];
  struct frame_module *prev;
  inst_t              cur;	/* Current, for adding */
  inst_t              ctxt;	/* Search context */
};

struct frame_jmp {
  struct frame base[1];
  jmp_buf      jmp_buf;
  int          code;
};

void frame_jmp(struct frame_jmp *fr, int code);

struct frame_block {
  struct frame_jmp   base[1];
  struct frame_block *prev;
  inst_t             dict;
};

struct frame_input {
  struct frame_jmp   base[1];
  struct frame_input *prev;
  char               *filename;
  struct stream      *str;
  struct tokbuf      tb[1];
};

struct frame_except {
  struct frame_jmp    base[1];
  struct frame_except *prev;
  inst_t              *arg;
};

struct {
  struct frame             *fp;
  struct frame_work        *wfp;
  struct frame_method_call *mcfp;
  struct frame_module      *modfp;
  struct frame_block       *blkfp;
  struct frame_input       *inpfp;
  struct frame_except      *exceptfp;
} oolvm[1];

static inline struct frame *
frame_push(unsigned size, unsigned type)
{
  struct frame *fr = mem_frame_alloc(size);

  fr->prev = oolvm->fp;
  fr->type = type;

  return (oolvm->fp = fr);
}

static inline void
frame_pop(unsigned size)
{
  oolvm->fp = oolvm->fp->prev;

  mem_frame_free(size);
}

static inline unsigned char *
frame_scratch_push(unsigned size)
{
  size = ((size - 1) & ~3) + 4;

  struct frame_scratch *fr = (struct frame_scratch *) frame_push(sizeof(struct frame_scratch) + size, FRAME_TYPE_SCRATCH);

  fr->size = size;

  return ((unsigned char *)(fr + 1));
}

static inline void
frame_scratch_pop(void)
{
  assert(oolvm->fp->type == FRAME_TYPE_SCRATCH);

  frame_pop(sizeof(struct frame) + ((struct frame_scratch *) oolvm->fp)->size);
}

static inline void
frame_work_push(unsigned size)
{
  struct frame_work *fr = (struct frame_work *) frame_push(sizeof(*fr) + size * sizeof(fr->data[0]), FRAME_TYPE_WORK);

  fr->prev = oolvm->wfp;
  memset(fr->data, 0, (fr->size = size) * sizeof(fr->data[0]));

  oolvm->wfp = fr;
}

static inline void
frame_work_pop(void)
{
  assert(oolvm->fp->type == FRAME_TYPE_WORK);
  assert(oolvm->wfp->base == oolvm->fp);

  inst_t   *p;
  unsigned size = oolvm->wfp->size, n;
  
  for (p = oolvm->wfp->data, n = size; n > 0; --n, ++p)  inst_release(*p);

  oolvm->wfp = oolvm->wfp->prev;
  frame_pop(sizeof(struct frame_work) + size * sizeof(oolvm->wfp->data[0]));
}

#define FRAME_WORK_BEGIN(_size)			\
  {						\
    frame_work_push((_size));

#define WORK(i)  (oolvm->wfp->data[i])

#define FRAME_WORK_END	 \
    frame_work_pop();    \
  }

static inline void
frame_method_call_push(inst_t *result, inst_t cl, inst_t sel, unsigned argc, inst_t *argv)
{
  struct frame_method_call *fr = (struct frame_method_call *) frame_push(sizeof(*fr), FRAME_TYPE_METHOD_CALL);

  fr->prev   = oolvm->mcfp;
  fr->result = result;
  fr->cl     = cl;
  fr->sel    = sel;
  fr->argc   = argc;
  fr->argv   = argv;

  oolvm->mcfp = fr;
}

static inline void
frame_method_call_pop(void)
{
  assert(oolvm->fp->type == FRAME_TYPE_METHOD_CALL);
  assert(oolvm->mcfp->base == oolvm->fp);

  oolvm->mcfp = oolvm->mcfp->prev;
  frame_pop(sizeof(struct frame_method_call));
}

#define FRAME_METHOD_CALL_BEGIN(_rslt, _cl, _sel, _argc, _argv)		\
  {									\
    frame_method_call_push((_rslt), (_cl), (_sel), (_argc), (_argv));

#define MC_RESULT  (oolvm->mcfp->result)
#define MC_ARGC    (oolvm->mcfp->argc)
#define MC_ARG(i)  (oolvm->mcfp->argv[i])
#define MC_SEL     (oolvm->mcfp->sel)

#define FRAME_METHOD_CALL_END	\
    frame_method_call_pop();    \
  }

static inline void
frame_module_push(inst_t cur, inst_t ctxt)
{
  struct frame_module *fr = (struct frame_module *) frame_push(sizeof(*fr), FRAME_TYPE_MODULE);

  fr->prev = oolvm->modfp;
  fr->cur  = cur;
  fr->ctxt = ctxt;

  oolvm->modfp = fr;
}

static inline void
frame_module_pop(void)
{
  assert(oolvm->fp->type == FRAME_TYPE_MODULE);
  assert(oolvm->modfp->base == oolvm->fp);

  oolvm->modfp = oolvm->modfp->prev;

  frame_pop(sizeof(struct frame_module));
}

#define FRAME_MODULE_BEGIN(_cur, _ctxt)		\
  {						\
    frame_module_push((_cur), (_ctxt));

#define MODULE_CUR   (oolvm->modfp->cur)
#define MODULE_CTXT  (oolvm->modfp->ctxt)

#define FRAME_MODULE_END \
    frame_module_pop();	 \
  }

static inline void
frame_block_push(inst_t dict)
{
  struct frame_block *fr = (struct frame_block *) frame_push(sizeof(*fr), FRAME_TYPE_BLOCK);

  fr->prev = oolvm->blkfp;
  fr->dict = dict;
  oolvm->blkfp = fr;
}

static inline void
frame_block_pop(void)
{
  assert(oolvm->fp->type == FRAME_TYPE_BLOCK);
  assert(oolvm->blkfp->base->base == oolvm->fp);

  oolvm->blkfp = oolvm->blkfp->prev;
  frame_pop(sizeof(struct frame_block));
}

#define FRAME_BLOCK_BEGIN(dict)						\
  {									\
    frame_block_push((dict));						\
    oolvm->blkfp->base->code = setjmp(oolvm->blkfp->base->jmp_buf);

#define FRAME_BLOCK_END \
    frame_block_pop();	\
  }

static inline void
frame_input_push(char *filename, struct stream *str)
{
  struct frame_input *fr = (struct frame_input *)  frame_push(sizeof(*fr), FRAME_TYPE_INPUT);

  fr->filename = filename;
  fr->str      = str;
  tokbuf_init(fr->tb);

  fr->prev = oolvm->inpfp;
  oolvm->inpfp = fr;
}

static inline void
frame_input_pop(void)
{
  assert(oolvm->fp->type == FRAME_TYPE_INPUT);
  assert(oolvm->inpfp->base->base == oolvm->fp);

  tokbuf_fini(oolvm->inpfp->tb);

  oolvm->inpfp = oolvm->inpfp->prev;
  frame_pop(sizeof(struct frame_input));
}

#define FRAME_INPUT_BEGIN(_file, _str)			\
  {							\
    frame_input_push((_file), (_str));

#define FRAME_INPUT_END \
    frame_input_pop();	\
  }

static inline void
frame_except_push(inst_t *arg)
{
  struct frame_except *fr = (struct frame_except *) frame_push(sizeof(*fr), FRAME_TYPE_EXCEPT);

  fr->prev = oolvm->exceptfp;
  fr->arg     = arg;
  oolvm->exceptfp = fr;
}

static inline void
frame_except_pop(void)
{
  assert(oolvm->fp->type == FRAME_TYPE_EXCEPT);
  assert(oolvm->exceptfp->base->base == oolvm->fp);

  oolvm->exceptfp = oolvm->exceptfp->prev;
  frame_pop(sizeof(struct frame_except));
}

#define FRAME_EXCEPT_BEGIN(_arg)					\
  {									\
    frame_except_push((_arg));						\
    oolvm->exceptfp->base->code = setjmp(oolvm->exceptfp->base->jmp_buf);

#define FRAME_EXCEPT_CODE (oolvm->exceptfp->base->code)

#define FRAME_EXCEPT_END	  \
    frame_except_pop();		  \
  }

void __attribute__((noreturn)) except_raise(inst_t except, inst_t arg);
void __attribute__((noreturn)) fatal(char *msg);

struct init_cl {
  inst_t *cl, *name, *parent;
  unsigned inst_size;
  void (*init)(inst_t inst, inst_t cl, unsigned argc, va_list ap);
  void (*walk)(inst_t inst, inst_t cl, void (*func)(inst_t));
  void (*free)(inst_t inst, inst_t cl);
  void (*cl_init)(inst_t cl);
};

struct init_str {
  inst_t *str;
  char   *data;
};

struct init_method {
  inst_t   *cl;
  unsigned ofs;
  inst_t   *sel;
  void     (*func)(void);
};

struct init_code_module {
  struct list        list_node[1];
  inst_t             *consts;
  unsigned           consts_size;
  struct init_cl     *init_cl;
  unsigned           init_cl_size;
  struct init_str    *init_str;
  unsigned           init_str_size;
  struct init_method *init_method;
  unsigned           init_method_size;
};

void code_module_add(struct init_code_module *cm);
void code_module_del(struct init_code_module *cm);

unsigned round_up_to_power_of_2(unsigned n);
