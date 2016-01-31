#include <stdlib.h>
#include <assert.h>

#include "ool.h"

struct inst_process {
  struct inst base[1];
  struct {
    inst_t pid;
    inst_t stdin;
    inst_t stdout;
    inst_t stderr;
  } val[1];
};
#define PROCESSVAL(x)  (((struct inst_process *)(x))->val)

static struct {
  inst_t cl_process;

  inst_t str_pid;
  inst_t str_process;
  inst_t str_stderr;
  inst_t str_stdin;
  inst_t str_stdout;
} process_consts;

static void
process_init(inst_t inst, inst_t cl, unsigned argc, va_list ap)
{
  assert(argc >= 1);

  inst_t args = va_arg(ap, inst_t);
  --argc;

  int fd[3][2];

  unsigned i, j;

  for (i = 0; i < ARRAY_SIZE(fd); ++i) {
    fd[i][0] = fd[i][1] = -1;
  }
  for (i = 0; i < ARRAY_SIZE(fd); ++i) {
    if (pipe(&fd[i][0]) < 0)  goto error;
  }

  int pid;

  if ((pid = fork()) < 0) {
    goto error;
  }
  if (pid == 0) {
    /* Child */

    close(0);
    dup(fd[0][0]);
    close(fd[0][0]);
    close(fd[0][1]);
    close(1);
    dup(fd[1][1]);
    close(fd[1][0]);
    close(fd[1][1]);
    close(2);
    dup(fd[2][1]);
    close(fd[2][0]);
    close(fd[2][1]);

    unsigned nargs = list_len(args);
    inst_t   p;
    char     *argv[nargs + 1];
    unsigned i;

    for (p = args, i = 0; i < nargs; ++i, p = CDR(p)) {
      argv[i] = STRVAL(CAR(p))->data;
    }
    argv[i] = 0;
    
    execv(argv[0], &argv[1]);

    exit(1);
  }

  int_new(&PROCESSVAL(inst)->pid, pid);
  file_new(&PROCESSVAL(inst)->stdin,  fdopen(fd[0][1], "w"));
  file_new(&PROCESSVAL(inst)->stdout, fdopen(fd[1][0], "r"));
  file_new(&PROCESSVAL(inst)->stderr, fdopen(fd[2][0], "r"));

  close(fd[0][0]);
  close(fd[1][1]);
  close(fd[2][1]);

  inst_init_parent(inst, cl, argc, ap);

  return;
    
 error:
  for (i = 0; i < ARRAY_SIZE(fd); ++i) {
    for (j = 0; j < ARRAY_SIZE(fd[0]); ++j) {
      if (fd[i][j] >= 0)  close(fd[i][j]);
    }
  }
}

static void
process_walk(inst_t inst, inst_t cl, void (*func)(inst_t))
{
  (*func)(PROCESSVAL(inst)->pid);
  (*func)(PROCESSVAL(inst)->stdin);
  (*func)(PROCESSVAL(inst)->stdout);
  (*func)(PROCESSVAL(inst)->stderr);

  inst_walk_parent(inst, cl, func);
}

static void
process_free(inst_t inst, inst_t cl)
{
  kill(PROCESSVAL(inst)->pid, 15);

  inst_free_parent(inst, cl);
}

void
cm_process_new(void)
{
  FRAME_WORK_BEGIN(1) {
    inst_alloc(&WORK(0), process_consts.cl_process);
    inst_init(WORK(0), 1, MC_ARG(1));
    inst_assign(MC_RESULT, WORK(0));
  } FRAME_WORK_END;
}

void
cm_process_pid(void)
{
  inst_assign(MC_RESULT, PROCESSVAL(MC_ARG(0))->pid);
}

void
cm_process_stdin(void)
{
  inst_assign(MC_RESULT, PROCESSVAL(MC_ARG(0))->stdin);
}

void
cm_process_stdout(void)
{
  inst_assign(MC_RESULT, PROCESSVAL(MC_ARG(0))->stdout);
}

void
cm_process_stderr(void)
{
  inst_assign(MC_RESULT, PROCESSVAL(MC_ARG(0))->stderr);
}

static struct init_cl process_init_cl[] = {
  { &process_consts.cl_process, &process_consts.str_process, &consts.cl_object, sizeof(struct inst_process), process_init, process_walk, process_free },
};

static struct init_str process_init_str[] = {
  { &process_consts.str_pid,     "pid" },
  { &process_consts.str_process, "Process" },
  { &process_consts.str_stderr,  "stderr" },
  { &process_consts.str_stdin,   "stdin" },
  { &process_consts.str_stdout,  "stdout" }
};

static struct init_method process_init_method[] = {
  { &process_consts.cl_process, CLASSVAL_OFS(cl_methods), &consts.str_newc, cm_process_new },

  { &process_consts.cl_process, CLASSVAL_OFS(inst_methods), &process_consts.str_pid,    cm_process_pid },
  { &process_consts.cl_process, CLASSVAL_OFS(inst_methods), &process_consts.str_stdin,  cm_process_stdin },
  { &process_consts.cl_process, CLASSVAL_OFS(inst_methods), &process_consts.str_stdout, cm_process_stdout },
  { &process_consts.cl_process, CLASSVAL_OFS(inst_methods), &process_consts.str_stderr, cm_process_stderr },
};

struct init_code_module process_code_module[1] = {
  { .consts           = (inst_t *) &process_consts,
    .consts_size      = sizeof(process_consts) / sizeof(inst_t),
    .init_cl          = process_init_cl,
    .init_cl_size     = ARRAY_SIZE(process_init_cl),
    .init_str         = process_init_str,
    .init_str_size    = ARRAY_SIZE(process_init_str),
    .init_method      = process_init_method,
    .init_method_size = ARRAY_SIZE(process_init_method)
  }
};

void __attribute__((constructor))
process_module_init(void)
{
  code_module_add(process_code_module);
}

void __attribute__((destructor))
process_module_fini(void)
{
  code_module_del(process_code_module);
}
