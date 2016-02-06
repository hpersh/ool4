#include <netdb.h>
#include <assert.h>

#include "ool.h"

static struct {
  inst_t cl_net;

  inst_t str_gethostbynamec;
  inst_t str_net;
} net_consts;

static void
cm_net_gethostbyname(void)
{
  if (MC_ARGC != 2)  error_argc();
  if (inst_of(MC_ARG(1)) != consts.cl_str)  error_bad_arg(MC_ARG(1));

  struct hostent *he = gethostbyname(STRVAL(MC_ARG(1))->data);
  if (he == 0 || he->h_addrtype != AF_INET || he->h_length != 4) {
    inst_assign(MC_RESULT, 0);
    return;
  }

  FRAME_WORK_BEGIN(2) {
    unsigned char *p;
    unsigned n;
    for (p = (unsigned char *) &he->h_addr[3], n = 4; n > 0; --n, --p) {
      int_new(&WORK(1), *p);
      list_new(&WORK(0), WORK(1), WORK(0));
    }
    inst_assign(MC_RESULT, WORK(0));
  } FRAME_WORK_END;
}

static struct init_cl net_init_cl[] = {
  { &net_consts.cl_net, &net_consts.str_net, &consts.cl_object, sizeof(struct inst) }
};

static struct init_str net_init_str[] = {
  { &net_consts.str_gethostbynamec, "gethostbyname:" },
  { &net_consts.str_net,            "Net" }
};

static struct init_method net_init_method[] = {
  { &net_consts.cl_net, CLASSVAL_OFS(cl_methods), &net_consts.str_gethostbynamec, cm_net_gethostbyname }
};

static struct init_code_module net_code_module[1] = {
  { .consts           = (inst_t *) &net_consts,
    .consts_size      = sizeof(net_consts) / sizeof(inst_t),
    .init_cl          = net_init_cl,
    .init_cl_size     = ARRAY_SIZE(net_init_cl),
    .init_str         = net_init_str,
    .init_str_size    = ARRAY_SIZE(net_init_str),
    .init_method      = net_init_method,
    .init_method_size = ARRAY_SIZE(net_init_method)
  }
};

void __attribute__((constructor))
net_module_init(void)
{
  code_module_add(net_code_module);
}

void __attribute__((destructor))
net_module_fini(void)
{
  code_module_del(net_code_module);
}
