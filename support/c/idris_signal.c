#include "idris_signal.h"

#include <stdlib.h>
#include <stdio.h>
#include <signal.h>

#ifdef _WIN32
#include <windows.h>
HANDLE ghMutex;
#include <pthread.h>
// static pthread_mutex_t sig_mutex = PTHREAD_MUTEX_INITIALIZER;
#endif

// ring buffer style storage for collected
// signals.
static int signal_buf_cap = 0;
static int signals_in_buf = 0;
static int signal_buf_next_read_idx = 0;
static int *signal_buf = NULL;

void _init_buf() {
  if (signal_buf == NULL) {
    signal_buf_cap = 10;
    signal_buf = malloc(sizeof(int) * signal_buf_cap);
  }
}

void _collect_signal(int signum);

void _collect_signal_core(int signum) {
  _init_buf();

  // FIXME: allow for adjusting capacity of signal buffer
  // instead of ignoring new signals when at capacity.
  if (signals_in_buf == signal_buf_cap) {
    return;
  }

  int write_idx = (signal_buf_next_read_idx + signals_in_buf) % signal_buf_cap;
  signal_buf[write_idx] = signum;
  signals_in_buf += 1;

#ifdef _WIN32
  //re-instate signal handler
  signal(signum, _collect_signal);
#endif
}

int raise_signal(int signum) {
  return raise(signum);
}

int send_signal(int pid, int signum) {
#ifdef _WIN32
  return raise_signal(signum);
#else
  return kill(pid, signum);
#endif
}

int sighup() {
#ifdef _WIN32
  return -1;
#else
  return SIGHUP;
#endif
}

int sigint() {
  return SIGINT;
}

int sigabrt() {
  return SIGABRT;
}

int sigquit() {
#ifdef _WIN32
  return -1;
#else
  return SIGQUIT;
#endif
}

int sigill() {
  return SIGILL;
}

int sigsegv() {
  return SIGSEGV;
}

int sigtrap() {
#ifdef _WIN32
  return -1;
#else
  return SIGTRAP;
#endif
}

int sigfpe() {
  return SIGFPE;
}

int sigusr1() {
#ifdef _WIN32
  return -1;
#else
  return SIGUSR1;
#endif
}

int sigusr2() {
#ifdef _WIN32
  return -1;
#else
  return SIGUSR2;
#endif
}

