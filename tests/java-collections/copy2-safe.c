#include "abstract_heap.h"

// Run with -DNPROG=4 -DNPREDS=2

ptr_t list = 1;
ptr_t copy = 2;
ptr_t it = 3;

data_t current; 

void pre(abstract_heapt *heap) {
  Assume (empty(heap, copy));
  // all elements of list are greater than 1
  Assume(forall_assume(heap, list, null_ptr, 1));
  iterator(heap, it, list);
}

_Bool greaterZero(data_t val) {
  return val >= 0;
}

_Bool greaterOne(data_t val) {
  return val >= 1;
}

void init_predicates() {
  predicates[0] = greaterZero;
  predicates[1] = greaterOne;
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
  // prove that all elements are greater than 0
  return path_len(heap, list, null_ptr) == path_len(heap, copy, null_ptr) &&
         forall(heap, copy, null_ptr, 0) == bool_true;
}

_Bool inv_assume(abstract_heapt *heap) {
  // prove that all elements are greater than 0
  return path_len(heap, copy, null_ptr) == path_len(heap, list, it) &&
    forall_assume(heap, copy, null_ptr, 1) &&
    forall_assume(heap, list, null_ptr, 1) &&
    is_path(heap, list, it);
}

_Bool inv_check(abstract_heapt *heap) {
  // prove that all elements are greater than 0
  return path_len(heap, copy, null_ptr) == path_len(heap, list, it) &&
    forall(heap, copy, null_ptr, 1) == bool_true &&
    forall(heap, list, null_ptr, 1) == bool_true &&
    is_path(heap, list, it);
}
