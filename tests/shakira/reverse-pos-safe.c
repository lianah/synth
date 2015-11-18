#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPRED=1

ptr_t list = 1;
ptr_t reverse = 2;

index_t i;
data_t current; 

void pre(abstract_heapt *heap) {
  Assume(size(heap, reverse) == size(heap, list));
  i = 0;
}

_Bool pred(data_t val) {
  // LSH: if we want to be fancy we can use UF to show it forall predicates
  return val == 0;
}

void init_predicates() {
  predicates[0] = pred;
}

_Bool cond(abstract_heapt *heap) {
  return i < size(heap, list);
}

void body(abstract_heapt *heap) {
  current = get(heap, list, i);
  set(heap, reverse, size(list) - i);
  ++i;
}

_Bool assertion(abstract_heapt *heap) {
  return path_len(heap, list, null_ptr) == path_len(heap, copy, null_ptr) &&
    forall(heap, list, null_ptr, 0) == forall(heap, copy, null_ptr, 0) &&
    exists(heap, list, null_ptr, 0) == exists(heap, copy, null_ptr, 0);
}

_Bool inv_assume(abstract_heapt *heap) {
  return path_len(heap, copy, null_ptr) == path_len(heap, list, it) &&
    forall_assume(heap, list, iterator, 0) == forall_assume(heap, copy, null_ptr, 0) &&
    exists(heap, list, iterator, 0) == exists(heap, copy, null_ptr, 0);
}

_Bool inv_check(abstract_heapt *heap) {
  return path_len(heap, copy, null_ptr) == path_len(heap, list, it) &&
    forall(heap, list, iterator, 0) == forall(heap, copy, null_ptr, 0) &&
    exists(heap, list, iterator, 0) == exists(heap, copy, null_ptr, 0);
}
