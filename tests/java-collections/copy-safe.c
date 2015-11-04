#include "abstract_heap.h"

// Run with -DNPROG=4 and -DNPRED=1

ptr_t list = 1;
ptr_t copy = 2;
ptr_t it = 3;

data_t current; 

void pre(abstract_heapt *heap) {
  abstract_new(heap, copy);
  iterator(heap, it, list);
}

_Bool pred(data_t val) {
  // LSH: if we want to be fancy we can use UF to show it forall predicates
  return val == 0;
}

void init_predicates() {
  predicates[0] = pred;
}

_Bool cond(abstract_heapt *heap) {
  return has_next(heap, it);
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

_Bool inv(abstract_heapt *heap) {
  return path_len(heap, copy, null_ptr) == path_len(heap, list, it) &&
    !is_path(heap, copy, list) &&
    (!is_path(heap, list, copy) || is_null(heap, copy))  &&
    is_path(heap, list, it) &&
    forall(heap, list, it, 0) == forall(heap, copy, null_ptr, 0) &&
    exists(heap, list, it, 0) == exists(heap, copy, null_ptr, 0);
}
