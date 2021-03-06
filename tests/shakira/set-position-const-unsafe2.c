#include "abstract_heap.h"

// Run with -DNPROG=3 -DNPREDS=1


ptr_t list = 1;
ptr_t it = 2;

word_t idx;

_Bool isFour(data_t val) {
  return val == 4;
}

void init_predicates() {
  predicates[0] = isFour;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
  idx = nondet_word_t();
}

void pre(abstract_heapt *heap) {
  idx = 0;
}

_Bool cond(abstract_heapt *heap) {
  return 0 <= idx && idx < size(heap, list) - 1;
}

void body(abstract_heapt *heap) {
  setP(heap, list, idx, 4);
  idx++;
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, list, null_ptr, 0) == bool_true;
}

_Bool inv_assume(abstract_heapt *heap) {

  if (0 <= idx && idx <= size(heap, list)) {
    listIterator(heap, it, list, idx);
    return forall_assume(heap, list, it, 0);
  } else {
    return 0;
  }
}

_Bool inv_check(abstract_heapt *heap) {
  return inv_assume(heap);
}
