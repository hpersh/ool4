#include <stdlib.h>
#include <stdarg.h>
#include <assert.h>

#include "ool.h"

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
mem_free(void *p, unsigned size)
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
frame_jmp(struct frame_jmp *fr, int code)
{
  while (fp < fr->base) {
    switch (fp->type) {
    case FRAME_TYPE_WORK:
      frame_work_pop();
      break;
    case FRAME_TYPE_METHOD_CALL:
      frame_method_call_pop();
      break;
    case FRAME_TYPE_MODULE:
      frame_module_pop();
      break;
    case FRAME_TYPE_RESTART:
      frame_restart_pop();
      break;
    case FRAME_TYPE_INPUT:
      frame_input_pop();
      break;
    default:
      assert(0);
    }
  }

  longjmp(fr->jmp_buf, code);
}

void
inst_alloc(inst_t *dst, inst_t cl)
{
  inst_t inst = (inst_t) mem_allocz(CLASSVAL(cl)->inst_size);

  inst_assign(&inst->inst_of, cl);
  inst_assign(dst, inst);
}

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
  mem_free(inst, CLASSVAL(inst_of(inst))->inst_size);
}

void
cm_obj_new(void)
{
  if (CLASSVAL(MC_ARG(0))->init == 0) {
    fprintf(stderr, "Cannot instantiate\n");
    error();
  }

  inst_alloc(MC_RESULT, MC_ARG(0));
}

void
cm_obj_newc(void)
{
  if (CLASSVAL(MC_ARG(0))->init == 0) {
    fprintf(stderr, "Cannot instantiate\n");
    error();
  }

  FRAME_WORK_BEGIN(1) {
    inst_alloc(&WORK(0), MC_ARG(0));
    inst_init(WORK(0), 1, MC_ARG(1));
    inst_assign(MC_RESULT, WORK(0));
  } FRAME_WORK_END;
}

void
cm_obj_quote(void)
{
  inst_assign(MC_RESULT, MC_ARG(0));
}

void
cm_obj_eval(void)
{
  inst_assign(MC_RESULT, MC_ARG(0));
}

void
cm_obj_tostring(void)
{
  inst_t cl_name = CLASSVAL(inst_of(MC_ARG(0)))->name;
  unsigned n = 1 + (STRVAL(cl_name)->size - 1) + 1 + 18 + 1 + 1;
  char buf[n];

  snprintf(buf, n, "<%s@%p>", STRVAL(cl_name)->data, MC_ARG(0));

  str_newc(MC_RESULT, 1, strlen(buf) + 1, buf);
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
bool_new(inst_t *dst, bool val)
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
cm_int_tostring(void)
{
  char buf[32];

  snprintf(buf, sizeof(buf), "%lld", INTVAL(MC_ARG(0)));

  str_newc(MC_RESULT, 1, strlen(buf) + 1, buf);
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
  mem_free(STRVAL(inst)->data, STRVAL(inst)->size);
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

bool
str_equal(inst_t s1, inst_t s2)
{
  return (STRVAL(s1)->size == STRVAL(s2)->size
	  && memcmp(STRVAL(s1)->data, STRVAL(s2)->data, STRVAL(s1)->size) == 0
	  );
}

void
cm_str_eval(void)
{
  FRAME_WORK_BEGIN(2) {
    inst_assign(&WORK(0), consts.cl_env);
    inst_assign(&WORK(1), MC_ARG(0));
    inst_method_call(MC_RESULT, consts.str_atc, 2, &WORK(0));
  } FRAME_WORK_END;
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

unsigned
list_len(inst_t li)
{
  unsigned result;

  for (result = 0; li != 0; li = CDR(li))  ++result;

  return (result);
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
  inst_t sel = METHODCALL_SEL(MC_ARG(0)), args = METHODCALL_ARGS(MC_ARG(0));
  bool   noevalf = STRVAL(sel)->size > 1 && STRVAL(sel)->data[0] == '&';
  unsigned nargs = list_len(args);
  
  FRAME_WORK_BEGIN(1) {
    array_new(&WORK(0), nargs);
    inst_t *p;
    for (p = ARRAYVAL(WORK(0))->data; nargs > 0; --nargs, ++p, args = CDR(args)) {
      if (noevalf) {
	inst_assign(p, CAR(args));
	continue;
      }
      inst_method_call(p, consts.str_eval, 1, &CAR(args));
    }
    inst_method_call(MC_RESULT, sel, ARRAYVAL(WORK(0))->size, ARRAYVAL(WORK(0))->data);
  } FRAME_WORK_END;
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
  mem_free(ARRAYVAL(inst)->data, ARRAYVAL(inst)->size * sizeof(ARRAYVAL(inst)->data[0]));

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
      goto done;
    }
    
    fprintf(stderr, "Bad method\n");
    error();

  done:
    ;
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
  { &consts.cl_module,      &consts.str_module,      &consts.cl_dict,   sizeof(struct inst_module),      module_init,      module_walk,      inst_free_parent },
  { &consts.cl_env,         &consts.str_environment, &consts.cl_object, sizeof(struct inst) },
  { &consts.cl_system,      &consts.str_system,      &consts.cl_object, sizeof(struct inst) }
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
  { &consts.str_new,         "new" },
  { &consts.str_newc,        "new:" },
  { &consts.str_object,      "#Object" },
  { &consts.str_pair,        "#Pair" },
  { &consts.str_quote,       "&quote" },
  { &consts.str_string,      "#String" },
  { &consts.str_system,      "#System" },
  { &consts.str_tostring,    "tostring" },
  { &consts.str_true,        "#true" }
};

struct {
  inst_t   *cl;
  unsigned ofs;
  inst_t   *sel;
  void     (*func)(void);
} init_method_tbl[] = {
  { &consts.cl_object, CLASSVAL_OFS(inst_methods), &consts.str_quote,    cm_obj_quote },
  { &consts.cl_object, CLASSVAL_OFS(inst_methods), &consts.str_eval,     cm_obj_eval },
  { &consts.cl_object, CLASSVAL_OFS(inst_methods), &consts.str_tostring, cm_obj_tostring },

  { &consts.cl_bool, CLASSVAL_OFS(inst_methods), &consts.str_andc, cm_bool_and },

  { &consts.cl_int, CLASSVAL_OFS(inst_methods), &consts.str_addc,     cm_int_add },
  { &consts.cl_int, CLASSVAL_OFS(inst_methods), &consts.str_tostring, cm_int_tostring },

  { &consts.cl_str, CLASSVAL_OFS(inst_methods), &consts.str_eval, cm_str_eval },

  { &consts.cl_method_call, CLASSVAL_OFS(inst_methods), &consts.str_eval, cm_method_call_eval },

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

    inst_assign(&CLASSVAL(consts.metaclass)->name, consts.str_metaclass);
    strdict_new(&CLASSVAL(consts.metaclass)->cl_vars,    32);
    strdict_new(&CLASSVAL(consts.metaclass)->cl_methods, 32);
    strdict_new(&CLASSVAL(consts.metaclass)->inst_vars,    32);
    strdict_new(&CLASSVAL(consts.metaclass)->inst_methods, 32);

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

  struct stream_file str[1];

  stream_file_init(str, stdin);

  FRAME_MODULE_BEGIN(consts.module_main) {
    FRAME_WORK_BEGIN(1) {
      FRAME_INPUT_BEGIN(str->base) {
	for (;;) {
	  parse_ctxt_init(FRAME_INPUT_PC, FRAME_INPUT_STR);
	  unsigned rc = parse(&WORK(0), FRAME_INPUT_PC);
	  if (rc == PARSE_EOF)  break;
	  parse_ctxt_fini(FRAME_INPUT_PC);
	  if (rc == PARSE_ERR) {
	    fprintf(stderr, "Syntax error\n");
	    continue;
	  }
	  inst_method_call(&WORK(0), consts.str_eval, 1, &WORK(0));
	  inst_method_call(&WORK(0), consts.str_tostring, 1, &WORK(0));
	  printf("%s\n", STRVAL(WORK(0))->data);
	}
      } FRAME_INPUT_END;
    } FRAME_WORK_END;
  } FRAME_MODULE_END;

  return (0);
}
