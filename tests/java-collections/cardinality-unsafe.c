#include "abstract_heap.h"

// Run with -DNPROG=2 -DNPREDS=3

ptr_t list = 1;

void pre(abstract_heapt *heap) {
  Assume (! empty(heap, list));
  Assume (forall_assume(heap, list, null_ptr, 0) == 0);
  Assume (forall_assume(heap, list, null_ptr, 1) == 0);
  Assume (forall_assume(heap, list, null_ptr, 2) == 0);
}

_Bool isNot0(data_t val) {
  return val != 0;
}

_Bool isNot1(data_t val) {
  return val != 1;
}

_Bool isNot2(data_t val) {
  return val != 2;
}


void init_predicates() {
  // initialize predicates
  predicates[0] = isNot0;
  predicates[1] = isNot1;
  predicates[2] = isNot2;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
}

_Bool cond(abstract_heapt *heap) {
  return 0;
}

void body(abstract_heapt *heap) {
}

_Bool assertion(abstract_heapt *heap) {
  return path_len(heap, list, null_ptr) >= 4;
}

_Bool inv_assume(abstract_heapt *heap) {
  return ! empty(heap, list)
    && forall_assume(heap, list, null_ptr, 0) == 0
    && forall_assume(heap, list, null_ptr, 1) == 0
    && forall_assume(heap, list, null_ptr, 2) == 0;
}

_Bool inv_check(abstract_heapt *heap) {
  return 1;
}
