struct inst;
typedef struct inst *inst_t;

struct inst {
  unsigned ref_cnt;
  inst_t   inst_of;
};

struct inst_bool {
  struct inst base[1];
  unsigned    val;
};
#define BOOLVAL(x)  (((struct inst_bool *)(x))->val)

typedef long long intval_t;

struct inst_int {
  struct inst base[1];
  intval_t    val;
};
#define INTVAL(x)  (((struct inst_int *)(x))->val)

struct inst_code_method {
  struct inst base[1];
  void        (*val)(void);
};
#define CODEMETHODVAL(x)  (((struct inst_code_method *)(x))->val)

struct inst_str {
  struct inst base[1];
  struct {
    unsigned size;
    char     *data;
  } val[1];
};
#define STRVAL(x)  (((struct inst_str *)(x))->val)

struct inst_dptr {
  struct inst base[1];
  struct {
    inst_t car, cdr;
  } val[1];
};
#define CAR(x)  (((struct inst_dptr *)(x))->val->car)
#define CDR(x)  (((struct inst_dptr *)(x))->val->cdr)

#define METHODCALL_SEL(x)   (CAR(x))
#define METHODCALL_ARGS(x)  (CDR(x))

#define BLOCK_ARGS(x)  (CAR(x))
#define BLOCK_BODY(x)  (CDR(x))

struct inst_array {
  struct inst base[1];
  struct {
    unsigned size;
    inst_t   *data;
  } val[1];
};
#define ARRAYVAL(x)  (((struct inst_array *)(x))->val)

struct inst_set {
  struct inst_array base[1];
  struct {
    inst_t   *(*find)(inst_t, inst_t, inst_t **);
    unsigned cnt;
  } val[1];
};
#define SETVAL(x)  (((struct inst_set *)(x))->val)

struct inst_module {
  struct inst_set base[1];
  struct {
    inst_t name, parent;
  } val[1];
};
#define MODULEVAL(x)  (((struct inst_module *)(x))->val)

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
  inst_t module_main;
  inst_t metaclass;

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
  inst_t cl_module;
  inst_t cl_env;
  inst_t cl_system;
  
  inst_t str_addc;
  inst_t str_andc;
  inst_t str_atc;
  inst_t str_atc_defc;
  inst_t str_atc_putc;
  inst_t str_array;
  inst_t str_boolean;
  inst_t str_block;
  inst_t str_code_method;
  inst_t str_dictionary;
  inst_t str_dptr;
  inst_t str_environment;
  inst_t str_equalc;
  inst_t str_eval;
  inst_t str_evalc;
  inst_t str_false;
  inst_t str_hash;
  inst_t str_integer; 
  inst_t str_list;
  inst_t str_main;
  inst_t str_metaclass;
  inst_t str_method_call;
  inst_t str_module;
  inst_t str_object;
  inst_t str_pair;
  inst_t str_string;
  inst_t str_system;
  inst_t str_true;
} consts;

enum {
  FRAME_TYPE_WORK,
  FRAME_TYPE_METHOD_CALL,
  FRAME_TYPE_MODULE
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

void inst_release(inst_t inst);

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

#define FRAME_METHOD_CALL_END	\
    frame_method_call_pop();    \
  }

struct frame_module {
  struct frame base[1];
  struct frame_module *prev;
  inst_t              module;
};

struct frame_module *modfp;

static inline void
frame_module_push(struct frame_module *fr, inst_t module)
{
  frame_push(fr->base, FRAME_TYPE_MODULE);

  fr->prev   = modfp;
  fr->module = module;

  modfp = fr;
}

static inline void
frame_module_pop(void)
{
  modfp = modfp->prev;

  frame_pop();
}

#define FRAME_MODULE_BEGIN(_mod)		\
  {						\
    struct frame_module __fr[1];		\
    frame_module_push(__fr, (_mod));

#define FRAME_MODULE_END \
    frame_module_pop();	 \
  }

#define MODULE_CUR  (modfp->module)

void bool_new(inst_t *dst, unsigned val);
void int_new(inst_t *dst, intval_t val);
void code_method_new(inst_t *dst, void (*func)(void));
void str_newc(inst_t *dst, unsigned argc, ...);
void pair_new(inst_t *dst, inst_t car, inst_t cdr);
void list_new(inst_t *dst, inst_t car, inst_t cdr);
void method_call_new(inst_t *dst, inst_t sel, inst_t args);
void block_new(inst_t *dst, inst_t args, inst_t body);
void array_new(inst_t *dst, unsigned size);
void strdict_new(inst_t *dst, unsigned size);
void dict_new(inst_t *dst, unsigned size);
void module_new(inst_t *dst, inst_t name, inst_t parent);
