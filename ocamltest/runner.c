/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*             Sébastien Hinderer, projet Gallium, INRIA Paris           */
/*                                                                        */
/*   Copyright 2016 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

/* Run programs and log their stdout/stderr, etc., with an optional timer */

#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>
#include <errno.h>
#include <signal.h>

typedef char *array[];

typedef struct {
  const char *program;
  array *argv;
  array *envp;
  const char *stdout_filename;
  const char *stderr_filename;
  int timeout;
} command_settings;

static volatile int timeout_expired = 0;

/* is_defined(str) returns 1 iff str points to a non-empty string */
/* Otherwise returns 0 */
static inline int is_defined(const char *str)
{
  return (str != NULL) && (*str != '\0');
}

__attribute__((__noreturn__)) /* TODO: make sure compiler supports this */
void fatal_error_with_location(const char *file, int line, const char *msg)
{
  fprintf(stderr, "%s:%d: %s\n", file, line, msg);
  exit(EXIT_FAILURE);
}

#define fatal_error(msg) fatal_error_with_location(__FILE__, __LINE__, msg)

__attribute__((__noreturn__)) /* TODO: make sure compiler supports this */
void fatal_perror_with_location(const char *file, int line, const char *msg)
{
  fprintf(stderr, "%s:%d: ", file, line);
  perror(msg);
  exit(EXIT_FAILURE);
}

#define fatal_perror(msg) fatal_perror_with_location(__FILE__, __LINE__, msg)

void handle_alarm(int sig)
{
  if (sig!=SIGALRM)
  {
    char message[256];
    sprintf(message, "Received unexpected signal %s", strsignal(sig));
    fatal_error(message);
  }
  timeout_expired = 1;
}

int run_command_child(const command_settings *settings)
{
  int res;
  int stdout_fd = -1, stderr_fd = -1; /* -1 means not redirected */
  int flags = O_WRONLY | O_CREAT | O_TRUNC;
  int mode = 0666;

  if (setpgid(0, 0) == -1) fatal_perror("setpgid");

  if (is_defined(settings->stdout_filename))
  {
    stdout_fd = open(settings->stdout_filename, flags, mode);
    if (stdout_fd < 0) fatal_perror("open");
    if ( dup2(stdout_fd, STDOUT_FILENO) == -1 ) fatal_perror("dup2");
  }

  if (is_defined(settings->stderr_filename))
  {
    if (stdout_fd != -1)
    {
#ifdef __GLIBC__
      char *stdout_realpath, *stderr_realpath;
      stdout_realpath = realpath(settings->stdout_filename, NULL);
      if (stdout_realpath == NULL) fatal_perror("realpath");
      stderr_realpath = realpath(settings->stderr_filename, NULL);
      if ( (stderr_realpath == NULL)  && (errno != ENOENT) )
      {
        free(stdout_realpath);
        fatal_perror("realpath");
      }
#else
      char stdout_realpath[PATH_MAX], stderr_realpath[PATH_MAX];
      if (realpath(settings->stdout_filename, stdout_realpath) == NULL)
        fatal_perror("realpath");
      if ((realpath(settings->stderr_filename, stderr_realpath) == NULL) && (errno != ENOENT))
        fatal_perror("realpath");
#endif /* __GLIBC__ */
      if (strcmp(stdout_realpath, stderr_realpath) == 0)
        stderr_fd = stdout_fd;
#ifdef __GLIBC__
      free(stdout_realpath);
      free(stderr_realpath);
#endif /* __GLIBC__ */
    }
    if (stderr_fd == -1)
    {
      stderr_fd = open(settings->stderr_filename, flags, mode);
      if (stderr_fd == -1) fatal_perror("open");
    }
    if ( dup2(stderr_fd, STDERR_FILENO) == -1 ) fatal_perror("dup2");
  }

  res = execve(settings->program, *settings->argv, *settings->envp);

  fatal_perror("execve");
  return res;
}

int run_command_parent(const command_settings *settings, pid_t child_pid)
{
  int waiting = 1;
  int child_status, result;

  if (settings->timeout>0)
  {
    struct sigaction action;
    action.sa_handler = handle_alarm;
    sigemptyset(&action.sa_mask);
    action.sa_flags = SA_RESETHAND;
    if (sigaction(SIGALRM, &action, NULL) == -1) fatal_perror("sigaction");
    if (alarm(settings->timeout) == -1) fatal_perror("alarm");
  }

  while (waiting)
  {
    result = wait(&child_status);
    if (result == -1)
    {
      if ((settings->timeout > 0) && (errno==EINTR) && (timeout_expired))
      {
        timeout_expired = 0;
        fprintf(stderr, "Timeout expired, killing %s (pid=%d)\n",
          settings->program, child_pid);
        if (kill(-child_pid, SIGKILL) == -1) fatal_perror("kill");
      } else if (errno == ECHILD) waiting = 0;
      else fatal_perror("wait");
    }
  }

  if (WIFEXITED(child_status)) {
    int code = WEXITSTATUS(child_status);
    fprintf(stderr, "Child terminated, code=%d\n", code);
    return code;
  }
  if ( WIFSIGNALED(child_status) ) {
    int signal = WTERMSIG(child_status);
    int core = 0;
    char *corestr;
#ifdef WCOREDUMP
    core = WCOREDUMP(child_status);
#endif /* WCOREDUMP */
    corestr = core ? "" : "no ";
    fprintf(stderr,
      "Child got signal %d(%s), %score dumped\n",
      signal, strsignal(signal), corestr
    );
    if (core)
    {
      if ( access("core", F_OK) == -1)
        fprintf(stderr, "Could not find core file.\n");
      else {
        char corefile[strlen(settings->program) + 6];
        sprintf(corefile, "%s.core", settings->program);
        if ( rename("core", corefile) == -1)
          fprintf(stderr, "Tge core file exists but could not be renamed.\n");
        else
          fprintf(stderr,"The core file has been renamed to %s\n", corefile);
      }
    }
    return -signal;
  }
  fatal_error("Child neither terminated normally nor received a signal!?");
  return -1;
}

int run_command(const command_settings *settings)
{
  pid_t child_pid = fork();
  if (child_pid == -1) fatal_perror("fork");
  if (child_pid == 0) return run_command_child(settings);
  else return run_command_parent(settings, child_pid);
}

int main(int argc, char *argv[])
{
  int result;
  if (argc<2) fatal_error("Specify which program to execute");
  char *program = argv[1];
  char *args[] = { program, NULL };
  char *env[] = { NULL };
  command_settings settings;
  settings.program = program;
  /* Case 1:
    settings.stdout_filename = NULL;
    settings.stderr_filename = NULL;
  */
  /* Case 2:
    settings.stdout_filename = "/tmp/output";
    settings.stderr_filename = NULL;
  */
  /* Case 3:
    settings.stdout_filename = NULL;
    settings.stderr_filename = "/tmp/error";
  */
  /* Case 4:
    settings.stdout_filename = "/tmp/output";
    settings.stderr_filename = "/tmp/error";
  */
  /* Case 5:
    settings.stdout_filename = "/tmp/log";
    settings.stderr_filename = "/tmp/log";
  */
  settings.stdout_filename = settings.stderr_filename = NULL;
  settings.argv = &args;
  settings.envp = &env;
  settings.timeout = 2;
  result = run_command(&settings);
  fprintf(stderr, "run_command returned %d\n", result);
}
