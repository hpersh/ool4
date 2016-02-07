#include <unistd.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <assert.h>

#include "ool.h"

struct inst_socket {
  struct inst base[1];
  struct {
    int domain;
    int type;
    int fd;
  } val[1];
};
#define SOCKETVAL(x)  (((struct inst_socket *)(x))->val)

static struct {
  inst_t cl_socket;

  inst_t int_afinet;
  inst_t int_sock_dgram;
  inst_t int_sock_stream;

  inst_t str_afinet;
  inst_t str_bindc;
  inst_t str_connectc;
  inst_t str_socket;
  inst_t str_sock_dgram;
  inst_t str_sock_stream;
} socket_consts;

static void
socket_init(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
  assert(argc >= 3);

  SOCKETVAL(inst)->domain = va_arg(ap, int);
  SOCKETVAL(inst)->type   = va_arg(ap, int);
  SOCKETVAL(inst)->fd     = va_arg(ap, int);
  argc -= 3;

  inst_init_parent(inst, cl, argc, ap);
}

static void
socket_free(inst_t inst, inst_t cl)
{
  close(SOCKETVAL(inst)->fd);

  inst_free_parent(inst, cl);
}

static void
cm_socket_new(void)
{
  if (MC_ARGC != 2)  error_argc();
  if (inst_of(MC_ARG(1)) != consts.cl_pair)  error_bad_arg(MC_ARG(1));

  inst_t domain = CAR(MC_ARG(1)), type = CDR(MC_ARG(1));

  if (inst_of(domain) != consts.cl_int ||inst_of(type) != consts.cl_int) {
    error_bad_arg(MC_ARG(1));
  }
  
  int d = INTVAL(domain), t = INTVAL(type);
  int fd = socket(d, t, 0);
  if (fd < 0) {
    perror(0);
    error(0);
  }

  inst_alloc(MC_RESULT, socket_consts.cl_socket);
  inst_init(*MC_RESULT, 3, d, t, fd);
}

static void
cm_socket_afinet(void)
{
  inst_assign(MC_RESULT, socket_consts.int_afinet);
}

static void
cm_socket_sock_dgram(void)
{
  inst_assign(MC_RESULT, socket_consts.int_sock_dgram);
}

static void
cm_socket_sock_stream(void)
{
  inst_assign(MC_RESULT, socket_consts.int_sock_stream);
}

static void
sockaddr_in_parse(struct sockaddr_in *sa, inst_t arg)
{
  if (inst_of(arg) != consts.cl_pair
      || !is_list(CAR(arg))
      || list_len(CAR(arg)) != 4
      || inst_of(CDR(arg)) != consts.cl_int
      ) {
    error_bad_arg(arg);
  }
  
  sa->sin_family = AF_INET;
  inst_t   p;
  unsigned ipaddr;
  for (ipaddr = 0, p = CAR(arg); p != 0; p = CDR(p)) {
    if (inst_of(CAR(p)) != consts.cl_int)  error_bad_arg(arg);
    intval_t a = INTVAL(CAR(p));
    if (a < 0 || a > 255)  error_bad_arg(arg);
    
    ipaddr = (ipaddr << 8) + a;
  }
  sa->sin_addr.s_addr = htonl(ipaddr);
  intval_t port = INTVAL(CDR(arg));
  if (port < 0 || port > 0xffff)  error_bad_arg(arg);
  sa->sin_port = htons(port);
}

static void
cm_socket_bind(void)
{
  if (MC_ARGC != 2)  error_argc();
  if (inst_of(MC_ARG(0)) != socket_consts.cl_socket)  error_bad_arg(MC_ARG(0));
  
  switch (SOCKETVAL(MC_ARG(0))->domain) {
  case AF_INET:
    {
      struct sockaddr_in sa[1];
      sockaddr_in_parse(sa, MC_ARG(1));

      if (bind(SOCKETVAL(MC_ARG(0))->fd, (struct sockaddr *) sa, sizeof(*sa)) != 0) {
	perror(0);
	error(0);
      }
    }
    break;

  default:
    error("Unknown socket domain");
  }

  inst_assign(MC_RESULT, MC_ARG(0));
}

static void
cm_socket_connect(void)
{
  if (MC_ARGC != 2)  error_argc();
  if (inst_of(MC_ARG(0)) != socket_consts.cl_socket)  error_bad_arg(MC_ARG(0));
  
  switch (SOCKETVAL(MC_ARG(0))->domain) {
  case AF_INET:
    {
      struct sockaddr_in sa[1];
      sockaddr_in_parse(sa, MC_ARG(1));

      if (connect(SOCKETVAL(MC_ARG(0))->fd, (struct sockaddr *) sa, sizeof(*sa)) != 0) {
	perror(0);
	error(0);
      }
    }
    break;

  default:
    error("Unknown socket domain");
  }

  inst_assign(MC_RESULT, MC_ARG(0));  
}

static void
cm_socket_read(void)
{
  if (MC_ARGC != 2)  error_argc();
  if (inst_of(MC_ARG(0)) != socket_consts.cl_socket)  error_bad_arg(MC_ARG(0));
  if (inst_of(MC_ARG(1)) != consts.cl_int)            error_bad_arg(MC_ARG(1));

  unsigned n = INTVAL(MC_ARG(1));
  char *buf = mem_alloc(n, false);
  int rc = read(SOCKETVAL(MC_ARG(0))->fd, buf, n);
  if (rc < 0) {
    perror(0);
    error(0);
  }
  
  str_newc(MC_RESULT, 1, rc, buf);

  mem_free(buf, n);
}

static void
cm_socket_write(void)
{
  if (MC_ARGC != 2)  error_argc();
  if (inst_of(MC_ARG(0)) != socket_consts.cl_socket)  error_bad_arg(MC_ARG(0));
  if (inst_of(MC_ARG(1)) != consts.cl_str)            error_bad_arg(MC_ARG(1));

  int_new(MC_RESULT, write(SOCKETVAL(MC_ARG(0))->fd, STRVAL(MC_ARG(1))->data, STRVAL(MC_ARG(1))->size - 1));
}

static struct init_cl socket_init_cl[] = {
  { &socket_consts.cl_socket, &socket_consts.str_socket, &consts.cl_object, sizeof(struct inst_socket), socket_init, inst_walk_parent, socket_free },
};

static struct init_str socket_init_str[] = {
  { &socket_consts.str_afinet,      "AF_INET" },
  { &socket_consts.str_bindc,       "bind:" },
  { &socket_consts.str_connectc,    "connect:" },
  { &socket_consts.str_socket,      "Socket" },
  { &socket_consts.str_sock_dgram,  "SOCK_DGRAM" },
  { &socket_consts.str_sock_stream, "SOCK_STREAM" }
};

static struct init_method socket_init_method[] = {
  { &socket_consts.cl_socket, CLASSVAL_OFS(cl_methods), &consts.str_newc,               cm_socket_new },
  { &socket_consts.cl_socket, CLASSVAL_OFS(cl_methods), &socket_consts.str_afinet,      cm_socket_afinet },
  { &socket_consts.cl_socket, CLASSVAL_OFS(cl_methods), &socket_consts.str_sock_dgram,  cm_socket_sock_dgram },
  { &socket_consts.cl_socket, CLASSVAL_OFS(cl_methods), &socket_consts.str_sock_stream, cm_socket_sock_stream },

  { &socket_consts.cl_socket, CLASSVAL_OFS(inst_methods), &socket_consts.str_bindc,    cm_socket_bind },
  { &socket_consts.cl_socket, CLASSVAL_OFS(inst_methods), &socket_consts.str_connectc, cm_socket_connect },
  { &socket_consts.cl_socket, CLASSVAL_OFS(inst_methods), &consts.str_readc,           cm_socket_read },
  { &socket_consts.cl_socket, CLASSVAL_OFS(inst_methods), &consts.str_writec,          cm_socket_write }
};

static struct init_code_module socket_code_module[1] = {
  { .consts           = (inst_t *) &socket_consts,
    .consts_size      = sizeof(socket_consts) / sizeof(inst_t),
    .init_cl          = socket_init_cl,
    .init_cl_size     = ARRAY_SIZE(socket_init_cl),
    .init_str         = socket_init_str,
    .init_str_size    = ARRAY_SIZE(socket_init_str),
    .init_method      = socket_init_method,
    .init_method_size = ARRAY_SIZE(socket_init_method)
  }
};

void __attribute__((constructor))
socket_module_init(void)
{
  code_module_add(socket_code_module);

  int_new(&socket_consts.int_afinet,      AF_INET);
  int_new(&socket_consts.int_sock_dgram,  SOCK_DGRAM);
  int_new(&socket_consts.int_sock_stream, SOCK_STREAM);
}

void __attribute__((destructor))
socket_module_fini(void)
{
  code_module_del(socket_code_module);
}
