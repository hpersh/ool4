#include <math.h>
#include <assert.h>

#include "ool.h"

static struct {
  inst_t str_cos;
  inst_t str_sin;
  inst_t str_sqrt;
} math_consts;

void
cm_float_cos(void)
{
  float_new(MC_RESULT, cosl(FLOATVAL(MC_ARG(0))));
}

void
cm_float_sin(void)
{
  float_new(MC_RESULT, sinl(FLOATVAL(MC_ARG(0))));
}

void
cm_float_sqrt(void)
{
  float_new(MC_RESULT, sqrtl(FLOATVAL(MC_ARG(0))));
}

static struct init_str math_init_str[] = {
  { &math_consts.str_cos,  "cos" },
  { &math_consts.str_sin,  "sin" },
  { &math_consts.str_sqrt, "sqrt" }
};

static struct init_method math_init_method[] = {
  { &consts.cl_float, CLASSVAL_OFS(inst_methods), &math_consts.str_cos,  cm_float_cos },
  { &consts.cl_float, CLASSVAL_OFS(inst_methods), &math_consts.str_sin,  cm_float_sin },
  { &consts.cl_float, CLASSVAL_OFS(inst_methods), &math_consts.str_sqrt, cm_float_sqrt }
};

struct init_code_module math_code_module[1] = {
  { .consts           = (inst_t *) &math_consts,
    .consts_size      = sizeof(math_consts) / sizeof(inst_t),
    .init_str         = math_init_str,
    .init_str_size    = ARRAY_SIZE(math_init_str),
    .init_method      = math_init_method,
    .init_method_size = ARRAY_SIZE(math_init_method)
  }
};

void __attribute__((constructor))
math_module_init(void)
{
  code_module_add(math_code_module);
}

void __attribute__((destructor))
math_module_fini(void)
{
  code_module_del(math_code_module);
}
