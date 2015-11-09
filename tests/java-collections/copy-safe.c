#include "abstract_heap.h"

// Run with -DNPROG=4 -DNPRED=1

ptr_t list = 1;
ptr_t copy = 2;
ptr_t it = 3;

data_t current; 

void pre(abstract_heapt *heap) {
  assume (! empty(heap, list));
  assume (empty(heap, copy));

  iterator(heap, it, list);
}

_Bool pred(data_t val) {
  // LSH: if we want to be fancy we can use UF to show it forall predicates
  return val == 0;
}

void init_predicates() {
  // initialize predicates
  predicates[0] = pred;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[copy] = 0;
  heap->is_iterator[it] = 1;
}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it);
}

void body(abstract_heapt *heap) {
  current = next(heap, it);
  add(heap, copy, current);
}

_Bool assertion(abstract_heapt *heap) {
  return path_len(heap, list, null_ptr) == path_len(heap, copy, null_ptr) &&
    forall(heap, list, null_ptr, 0) == forall(heap, copy, null_ptr, 0) &&
    exists(heap, list, null_ptr, 0) == exists(heap, copy, null_ptr, 0);
}

_Bool inv_assume(abstract_heapt *heap) {
  return path_len(heap, copy, null_ptr) == path_len(heap, list, it) &&
    forall_assume(heap, list, it, 0) == forall_assume(heap, copy, null_ptr, 0) &&
    exists_assume(heap, list, it, 0) == exists_assume(heap, copy, null_ptr, 0);
}

_Bool inv_check(abstract_heapt *heap) {
  return path_len(heap, copy, null_ptr) == path_len(heap, list, it) &&
    forall(heap, list, it, 0) == forall(heap, copy, null_ptr, 0) &&
    exists(heap, list, it, 0) == exists(heap, copy, null_ptr, 0);
}
