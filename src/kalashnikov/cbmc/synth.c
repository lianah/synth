#include "synth.h"
void test(solution_t *solution, word_t args[NARGS]) {
  __CPROVER_assume(check(solution, args));
}

int main(void) {
  solution_t solution;
  int i;

  for (i = 0; i < NPROGS; i++) {
    __CPROVER_assume(wellformed(&solution.progs[i]));
    __CPROVER_assume(!exclude(&solution.progs[i]));
  }

  tests(&solution);

  assert(0);
}