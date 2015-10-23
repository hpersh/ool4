#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>

#define ARRAY_SIZE(a)  (sizeof(a) / sizeof((a)[0]))

#define PTR_TO_UINT(x)  ((unsigned long long)(x))
#define FIELD_OFS(s, f)  PTR_TO_UINT(&((s *) 0)->f)

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

inst_t
inst_of(inst_t inst)
{
  return (inst == 0 ? consts.cl_object : inst->inst_of);
}

void *
mem_alloc(unsigned size)
{
  void *result = malloc(size);

  assert(result != 0);

  return (result);
}

void *
mem_allocz(unsigned size)
{
  void *result = mem_alloc(size);

  memset(result, 0, size);

  return (result);
}

void
mem_free(void *p)
{
  free(p);
}

void
inst_free(inst_t inst)
{
  inst_t cl = inst_of(inst);

  (*CLASSVAL(cl)->free)(inst, cl);
}

inst_t
inst_retain(inst_t inst)
{
  if (inst != 0) {
    ++inst->ref_cnt;

    assert(inst->ref_cnt != 0);
  }

  return (inst);
}

void
inst_release(inst_t inst)
{
  if (inst == 0)  return;

  assert(inst->ref_cnt != 0);

  if (--inst->ref_cnt == 0)  inst_free(inst);
}

void
inst_assign(inst_t *dst, inst_t src)
{
  inst_t temp = inst_retain(*dst);

  *dst = inst_retain(src);
  inst_release(temp);
}

void
inst_alloc(inst_t *dst, inst_t cl)
{
  inst_t inst = (inst_t) mem_allocz(CLASSVAL(cl)->inst_size);

  inst_assign(&inst->inst_of, cl);
  inst_assign(dst, inst);
}

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

void
inst_init_parent(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
  inst_t parent = CLASSVAL(cl)->parent;

  (*CLASSVAL(parent)->init)(inst, parent, argc, ap);
}

void
inst_walk_parent(inst_t inst, inst_t cl, void (*func)(inst_t))
{
  inst_t parent = CLASSVAL(cl)->parent;

  (*CLASSVAL(parent)->walk)(inst, parent, func);
}

void
inst_free_parent(inst_t inst, inst_t cl)
{
  inst_t parent = CLASSVAL(cl)->parent;

  (*CLASSVAL(parent)->free)(inst, parent);
}

void
inst_init(inst_t inst, unsigned argc, ...)
{
  va_list ap;

  va_start(ap, argc);

  inst_t cl = inst_of(inst);

  (*CLASSVAL(cl)->init)(inst, cl, argc, ap);

  va_end(ap);
}

void inst_method_call(inst_t *dst, inst_t sel, unsigned argc, inst_t *argv);

void
error(void)
{
  abort();
}

void
object_init(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
  assert(argc == 0);
}

void
object_walk(inst_t inst, inst_t cl, void (*func)(inst_t))
{
}

void
object_free(inst_t inst, inst_t cl)
{
  mem_free(inst);
}

void
cm_obj_eval(void)
{
  inst_assign(MC_RESULT, MC_ARG(0));
}

void
bool_init(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  BOOLVAL(inst) = va_arg(ap, unsigned);
  --argc;

  inst_init_parent(inst, cl, argc, ap);
}

void
bool_new(inst_t *dst, unsigned val)
{
  inst_alloc(dst, consts.cl_bool);
  inst_init(*dst, 1, val);
}

void
cm_bool_and(void)
{
  bool_new(MC_RESULT, BOOLVAL(MC_ARG(0)) && BOOLVAL(MC_ARG(1)));
}

void
int_init(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  INTVAL(inst) = va_arg(ap, intval_t);
  --argc;

  inst_init_parent(inst, cl, argc, ap);
}

void
int_new(inst_t *dst, intval_t val)
{
  inst_alloc(dst, consts.cl_int);
  inst_init(*dst, 1, val);
}

void
cm_int_add(void)
{
  int_new(MC_RESULT, INTVAL(MC_ARG(0)) + INTVAL(MC_ARG(1)));
}

void
code_method_init(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  CODEMETHODVAL(inst) = va_arg(ap, void (*)(void));
  --argc;
  
  inst_init_parent(inst, cl, argc, ap);
}

void
code_method_new(inst_t *dst, void (*func)(void))
{
  inst_alloc(dst, consts.cl_code_method);
  inst_init(*dst, 1, func);
}

void
str_init(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
}

void
str_free(inst_t inst, inst_t cl)
{
  mem_free(STRVAL(inst)->data);
  inst_free_parent(inst, cl);
}

void
str_newc(inst_t *dst, unsigned argc, ...)
{
  FRAME_WORK_BEGIN(1) {
    va_list ap;
    
    va_start(ap, argc);
    
    unsigned len, n;
    char     *s;
    
    for (len = 0, n = argc; n > 0; --n) {
      len += va_arg(ap, unsigned) - 1;
      s   =  va_arg(ap, char *);
    }
    ++len;
    
    va_end(ap);
    
    inst_alloc(&WORK(0), consts.cl_str);
    STRVAL(WORK(0))->data = s = (char *) mem_alloc(STRVAL(WORK(0))->size = len);

    va_start(ap, argc);

    for (n = argc; n > 0; --n) {
      len = va_arg(ap, unsigned) - 1;
      memcpy(s, va_arg(ap, char *), len);
      s += len;
    }
    *s = 0;

    va_end(ap);

    inst_assign(dst, WORK(0));
  } FRAME_WORK_END;
}

unsigned
str_hash(inst_t s)
{
  unsigned result, n;
  char     *p;
  
  for (result = 0, p = STRVAL(s)->data, n = STRVAL(s)->size; n > 0; --n, ++p)  result += *p;

  return (result);
}

unsigned
str_equal(inst_t s1, inst_t s2)
{
  return (STRVAL(s1)->size == STRVAL(s2)->size
	  && memcmp(STRVAL(s1)->data, STRVAL(s2)->data, STRVAL(s1)->size) == 0
	  );
}

void
dptr_init(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
  assert(argc > 1);

  inst_assign(&CAR(inst), va_arg(ap, inst_t));
  inst_assign(&CDR(inst), va_arg(ap, inst_t));
  argc -= 2;

  inst_init_parent(inst, cl, argc, ap);
}

void
dptr_walk(inst_t inst, inst_t cl, void (*func)(inst_t))
{
  (*func)(CAR(inst));
  (*func)(CDR(inst));

  inst_walk_parent(inst, cl, func);
}

void
pair_new(inst_t *dst, inst_t car, inst_t cdr)
{
  FRAME_WORK_BEGIN(1) {
    inst_alloc(&WORK(0), consts.cl_pair);
    inst_init(WORK(0), 2, car, cdr);
    inst_assign(dst, WORK(0));
  } FRAME_WORK_END;
}

void
list_new(inst_t *dst, inst_t car, inst_t cdr)
{
  FRAME_WORK_BEGIN(1) {
    inst_alloc(&WORK(0), consts.cl_list);
    inst_init(WORK(0), 2, car, cdr);
    inst_assign(dst, WORK(0));
  } FRAME_WORK_END;
}

void
method_call_new(inst_t *dst, inst_t sel, inst_t args)
{
  FRAME_WORK_BEGIN(1) {
    inst_alloc(&WORK(0), consts.cl_method_call);
    inst_init(WORK(0), 2, sel, args);
    inst_assign(dst, WORK(0));
  } FRAME_WORK_END;
}

void
cm_method_call_eval(void)
{
  
}

void
block_new(inst_t *dst, inst_t args, inst_t body)
{
  FRAME_WORK_BEGIN(1) {
    inst_alloc(&WORK(0), consts.cl_method_call);
    inst_init(WORK(0), 2, args, body);
    inst_assign(dst, WORK(0));
  } FRAME_WORK_END;
}

inst_t *
strdict_find(inst_t dict, inst_t key, inst_t **bucket)
{
  inst_t *p = &ARRAYVAL(dict)->data[str_hash(key) & (ARRAYVAL(dict)->size - 1)];
  if (bucket != 0)  *bucket = p;
  inst_t q;
  for ( ; (q = *p) != 0; p = &CDR(q)) {
    if (str_equal(CAR(CAR(q)), key)) {
      return (p);
    }
  }

  return (0);
}

inst_t *
dict_find(inst_t dict, inst_t key, inst_t **bucket)
{
  inst_t *result = 0;

  FRAME_WORK_BEGIN(2) {
    inst_assign(&WORK(0), key);
    inst_method_call(&WORK(1), consts.str_hash, 1, &WORK(0));
    inst_t *p = &ARRAYVAL(dict)->data[INTVAL(WORK(1)) & (ARRAYVAL(dict)->size - 1)];
    if (bucket != 0)  *bucket = p;
    inst_t q;
    for ( ; (q = *p) != 0; p = &CDR(q)) {
      inst_assign(&WORK(1), CAR(CAR(q)));
      inst_method_call(&WORK(1), consts.str_equalc, 2, &WORK(0));
      if (BOOLVAL(WORK(1))) {
	result = p;
	break;
      }
    }
  } FRAME_WORK_END;

  return (result);
}

void
array_init(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  unsigned size = va_arg(ap, unsigned);
  --argc;

  ARRAYVAL(inst)->size = size;
  ARRAYVAL(inst)->data = mem_allocz(size * sizeof(ARRAYVAL(inst)->data[0]));

  inst_init_parent(inst, cl, argc, ap);
}

void
array_walk(inst_t inst, inst_t cl, void (*func)(inst_t))
{
  inst_t   *p;
  unsigned n;
  
  for (p = ARRAYVAL(inst)->data, n = ARRAYVAL(inst)->size; n > 0; --n, ++p) {
    (*func)(*p);
  }

  inst_walk_parent(inst, cl, func);
}

void
array_free(inst_t inst, inst_t cl)
{
  mem_free(ARRAYVAL(inst)->data);

  inst_free_parent(inst, cl);
}

void
array_new(inst_t *dst, unsigned size)
{
  inst_alloc(dst, consts.cl_array);
  inst_init(*dst, 1, size);
}

void
dict_init(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
  assert(argc > 0);

  SETVAL(inst)->find = va_arg(ap, inst_t *(*)(inst_t, inst_t, inst_t **));
  --argc;

  inst_init_parent(inst, cl, argc, ap);
}

unsigned
round_up_to_power_of_2(unsigned n)
{
  unsigned result = n, k;

  for (;;) {
    k = n & (n - 1);
    if (k == 0)  return (result);
    result = (n = k) << 1;
  }
}

void
strdict_new(inst_t *dst, unsigned size)
{
  inst_alloc(dst, consts.cl_dict);
  inst_init(*dst, 2, strdict_find, round_up_to_power_of_2(size));
}

void
dict_new(inst_t *dst, unsigned size)
{
  inst_alloc(dst, consts.cl_dict);
  inst_init(*dst, 2, dict_find, round_up_to_power_of_2(size));
}

inst_t
dict_at(inst_t dict, inst_t key)
{
  inst_t *p = (*SETVAL(dict)->find)(dict, key, 0);

  return (p == 0 ? 0 : CAR(*p));
}

void
dict_at_put(inst_t dict, inst_t key, inst_t val)
{
  inst_t *bucket, *p = (*SETVAL(dict)->find)(dict, key, &bucket);

  if (p == 0) {
    FRAME_WORK_BEGIN(1) {
      pair_new(&WORK(0), key, val);
      list_new(bucket, WORK(0), *bucket);
      ++SETVAL(dict)->cnt;
    } FRAME_WORK_END;

    return;
  }

  inst_assign(&CDR(CAR(*p)), val);
}

void
dict_del(inst_t dict, inst_t key)
{
  inst_t *p = (*SETVAL(dict)->find)(dict, key, 0);

  if (p == 0)  return;

  inst_assign(p, CDR(*p));
}

void
module_init(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
  assert(argc > 1);

  inst_assign(&MODULEVAL(inst)->name, va_arg(ap, inst_t));
  inst_assign(&MODULEVAL(inst)->parent, va_arg(ap, inst_t));
  argc -= 2;

  inst_init_parent(inst, cl, argc, ap);
}

void
module_walk(inst_t inst, inst_t cl, void (*func)(inst_t))
{
  (*func)(MODULEVAL(inst)->name);
  (*func)(MODULEVAL(inst)->parent);

  inst_walk_parent(inst, cl, func);
}

void
module_new(inst_t *dst, inst_t name, inst_t parent)
{
  FRAME_WORK_BEGIN(1) {
    inst_alloc(&WORK(0), consts.cl_module);
    inst_init(WORK(0), 4, name, parent, strdict_find, 32);
    inst_assign(dst, WORK(0));
  } FRAME_WORK_END;
}

inst_t *
env_find(inst_t var)
{
  struct frame_module *p;

  for (p = modfp; p != 0; p = p->prev) {
    inst_t q = dict_at(p->module, var);

    if (q != 0)  return (&CDR(q));
  }

  return (0);
}

inst_t
env_at(inst_t var)
{						
  inst_t *p = env_find(var);

  if (p == 0) {
    fprintf(stderr, "Symbol not bound\n");
    error();
  }

  return (*p);
}

void
env_at_put(inst_t var, inst_t val)
{
  inst_t *p = env_find(var);

  if (p == 0) {
    dict_at_put(MODULE_CUR, var, val);

    return;
  }

  inst_assign(p, val);
}

void
env_at_def(inst_t var, inst_t val)
{
  dict_at_put(MODULE_CUR, var, val);
}

void
cm_env_at(void)
{
  inst_assign(MC_RESULT, env_at(MC_ARG(1)));
}

void
cm_env_atput(void)
{
  env_at_put(MC_ARG(1), MC_ARG(2));

  inst_assign(MC_RESULT, MC_ARG(2));
}

void
cm_env_atdef(void)
{
  env_at_def(MC_ARG(1), MC_ARG(2));

  inst_assign(MC_RESULT, MC_ARG(2));
}

inst_t
method_find(inst_t sel, unsigned ofs, inst_t cl, inst_t *found_cl)
{
  for (*found_cl = cl; cl != 0; cl = CLASSVAL(cl)->parent) {
    inst_t pr = dict_at(*(inst_t *)((char *) cl + ofs), sel);

    if (pr != 0) {
      *found_cl = cl;

      return (CDR(pr));
    }
  }

  return (0);
}

void
inst_method_call(inst_t *dst, inst_t sel, unsigned argc, inst_t *argv)
{
  assert(argc > 0);

  inst_t f = 0, recvr = argv[0], cl = inst_of(recvr), found_cl;

  if (cl == consts.metaclass)  f = method_find(sel, CLASSVAL_OFS(cl_methods), recvr, &found_cl);
  if (f == 0)                  f = method_find(sel, CLASSVAL_OFS(inst_methods), cl, &found_cl);

  FRAME_METHOD_CALL_BEGIN(dst, found_cl, sel, argc, argv) {
    if (f == 0) {
      fprintf(stderr, "Method not found\n");
      error();
    }

    cl = inst_of(f);
    if (cl == consts.cl_code_method) {
      (*CODEMETHODVAL(f))();

      return;
    }
    
    fprintf(stderr, "Bad method\n");
    error();
  } FRAME_METHOD_CALL_END;
}

struct {
  inst_t *cl, *name, *parent;
    unsigned inst_size;
    void (*init)(inst_t inst, inst_t cl, unsigned argc, va_list ap);
    void (*walk)(inst_t inst, inst_t cl, void (*func)(inst_t));
    void (*free)(inst_t inst, inst_t cl);
} init_cl_tbl[] = {
  { &consts.cl_object,      &consts.str_object,                      0, sizeof(struct inst),             object_init,      object_walk,      object_free },
  { &consts.cl_bool,        &consts.str_boolean,     &consts.cl_object, sizeof(struct inst_bool),        bool_init,        inst_walk_parent, inst_free_parent },
  { &consts.cl_int,         &consts.str_integer,     &consts.cl_object, sizeof(struct inst_int),         int_init,         inst_walk_parent, inst_free_parent },
  { &consts.cl_code_method, &consts.str_code_method, &consts.cl_object, sizeof(struct inst_code_method), code_method_init, inst_walk_parent, inst_free_parent },
  { &consts.cl_str,         &consts.str_string,      &consts.cl_object, sizeof(struct inst_str),         str_init,         inst_walk_parent, str_free },
  { &consts.cl_dptr,        &consts.str_dptr,        &consts.cl_object, sizeof(struct inst_dptr),        dptr_init,        dptr_walk,        inst_free_parent },
  { &consts.cl_pair,        &consts.str_pair,        &consts.cl_dptr,   sizeof(struct inst_dptr),        inst_init_parent, inst_walk_parent, inst_free_parent },
  { &consts.cl_list,        &consts.str_list,        &consts.cl_dptr,   sizeof(struct inst_dptr),        inst_init_parent, inst_walk_parent, inst_free_parent },
  { &consts.cl_method_call, &consts.str_method_call, &consts.cl_dptr,   sizeof(struct inst_dptr),        inst_init_parent, inst_walk_parent, inst_free_parent },
  { &consts.cl_block,       &consts.str_block,       &consts.cl_dptr,   sizeof(struct inst_dptr),        inst_init_parent, inst_walk_parent, inst_free_parent },
  { &consts.cl_array,       &consts.str_array,       &consts.cl_object, sizeof(struct inst_array),       array_init,       array_walk,       array_free },
  { &consts.cl_dict,        &consts.str_dictionary,  &consts.cl_array,  sizeof(struct inst_set),         dict_init,        inst_walk_parent, inst_free_parent },
  { &consts.cl_module,      &consts.str_module,      &consts.cl_dict,   sizeof(struct inst_module),      module_init,      module_walk,      inst_free_parent }
};

struct {
  inst_t *str;
  char   *data;
} init_str_tbl[] = {
  { &consts.str_addc,        "add:" },
  { &consts.str_andc,        "and:" },
  { &consts.str_atc,         "at:" },
  { &consts.str_atc_defc,    "at:def:" },
  { &consts.str_atc_putc,    "at:put:" },
  { &consts.str_array,       "#Array" },
  { &consts.str_boolean,     "#Boolean" },
  { &consts.str_block,       "#Block" },
  { &consts.str_code_method, "#Code_Method" },
  { &consts.str_dictionary,  "#Dictionary" },
  { &consts.str_dptr,        "#Dptr" },
  { &consts.str_environment, "#Environment" },
  { &consts.str_equalc,      "equal:" },
  { &consts.str_eval,        "eval" },
  { &consts.str_evalc,       "eval:" },
  { &consts.str_false,       "#false" },
  { &consts.str_integer,     "#Integer" },
  { &consts.str_list,        "#List" },
  { &consts.str_main,        "#main" },
  { &consts.str_metaclass,   "#Metaclass" },
  { &consts.str_method_call, "#Method_Call" },
  { &consts.str_module,      "#Module" },
  { &consts.str_object,      "#Object" },
  { &consts.str_pair,        "#Pair" },
  { &consts.str_string,      "#String" },
  { &consts.str_system,      "#System" },
  { &consts.str_true,        "#true" }
};

struct {
  inst_t   *cl;
  unsigned ofs;
  inst_t   *sel;
  void     (*func)(void);
} init_method_tbl[] = {
  { &consts.cl_object, CLASSVAL_OFS(inst_methods), &consts.str_eval, cm_obj_eval },

  { &consts.cl_bool, CLASSVAL_OFS(inst_methods), &consts.str_andc, cm_bool_and },

  { &consts.cl_int, CLASSVAL_OFS(inst_methods), &consts.str_addc, cm_int_add },

  { &consts.cl_env, CLASSVAL_OFS(cl_methods), &consts.str_atc,      cm_env_at },
  { &consts.cl_env, CLASSVAL_OFS(cl_methods), &consts.str_atc_defc, cm_env_atdef },
  { &consts.cl_env, CLASSVAL_OFS(cl_methods), &consts.str_atc_putc, cm_env_atput }
};

void
init(void)
{
  FRAME_WORK_BEGIN(1) {
    /* Pass 1 - Create metaclass */

    consts.metaclass = (inst_t) mem_allocz(sizeof(struct inst_metaclass));
    CLASSVAL(consts.metaclass)->inst_size = sizeof(struct inst_metaclass);

    /* Pass 2 - Create classes */

    unsigned i;

    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
      inst_alloc(init_cl_tbl[i].cl, consts.metaclass);
      if (init_cl_tbl[i].parent != 0) {
	inst_assign(&CLASSVAL(*init_cl_tbl[i].cl)->parent, *init_cl_tbl[i].parent);
      }
      CLASSVAL(*init_cl_tbl[i].cl)->inst_size = init_cl_tbl[i].inst_size;
      CLASSVAL(*init_cl_tbl[i].cl)->init      = init_cl_tbl[i].init;
      CLASSVAL(*init_cl_tbl[i].cl)->walk      = init_cl_tbl[i].walk;
      CLASSVAL(*init_cl_tbl[i].cl)->free      = init_cl_tbl[i].free;
    }

    /* Pass 3 - Create strings */

    for (i = 0; i < ARRAY_SIZE(init_str_tbl); ++i) {
      str_newc(init_str_tbl[i].str, 1, strlen(init_str_tbl[i].data) + 1, init_str_tbl[i].data);
    }

    /* Pass 4 - Fix-up classes */

    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
      inst_assign(&CLASSVAL(*init_cl_tbl[i].cl)->name,   *init_cl_tbl[i].name);
      strdict_new(&CLASSVAL(*init_cl_tbl[i].cl)->cl_vars,    32);
      strdict_new(&CLASSVAL(*init_cl_tbl[i].cl)->cl_methods, 32);
      strdict_new(&CLASSVAL(*init_cl_tbl[i].cl)->inst_vars,    32);
      strdict_new(&CLASSVAL(*init_cl_tbl[i].cl)->inst_methods, 32);
    }  

    /* Pass 5 - Create methods */

    for (i = 0; i < ARRAY_SIZE(init_method_tbl); ++i) {
      code_method_new(&WORK(0), init_method_tbl[i].func);
      dict_at_put(*(inst_t *)((char *)*init_method_tbl[i].cl + init_method_tbl[i].ofs), *init_method_tbl[i].sel, WORK(0));
    }

    /* Pass 6 - Create main module */

    module_new(&consts.module_main, consts.str_main, 0);
    dict_at_put(consts.module_main, consts.str_main, consts.module_main);
    dict_at_put(consts.module_main, consts.str_metaclass, consts.metaclass);
    bool_new(&WORK(0), 1);
    dict_at_put(consts.module_main, consts.str_true, WORK(0));
    bool_new(&WORK(0), 0);
    dict_at_put(consts.module_main, consts.str_false, WORK(0));
    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
      dict_at_put(consts.module_main, *init_cl_tbl[i].name, *init_cl_tbl[i].cl);
    }

  } FRAME_WORK_END;
}

int
main(void)
{
  init();

  FRAME_WORK_BEGIN(10) {
    int_new(&WORK(0), 13);
    int_new(&WORK(1), 42);
    inst_method_call(&WORK(2), consts.str_addc, 2, &WORK(0));
    
  } FRAME_WORK_END;
  
  return (0);
}
