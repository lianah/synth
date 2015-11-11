#include "abstract_heap.h"

// Run with -DNPROG=5 and -DNPRED=1

ptr_t list = 1;
ptr_t less = 2;
ptr_t greater = 3;
ptr_t iterator = 4;

data_t pivot;

_Bool isLess(data_t val) {
  return val <= pivot;
}

void init_predicates() {  
  predicates[0] = isLess;
}

void pre(abstract_heapt *heap) {
  assign(heap, iterator, list);
}

_Bool cond(abstract_heapt *heap) {
  return has_next(heap, iterator);
}

void body(abstract_heapt *heap) {
  current = next(heap, iterator);
  if (isLess(current)) {
    add(heap, less, current);
  } else {
    add(heap, greater, current);
  }
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, less, null_ptr, 0) == bool_true
    && forall (heap, greater, null_ptr, 0) == bool_false
    && path_len(heap, less, null_ptr) + path_len(heap, greater, null_ptr) = path_len(heap, list, null_ptr);
}

_Bool inv_assume(abstract_heapt *heap) {
  return forall_assume(heap, less, null_ptr, 0) == bool_true
    && forall_assume (heap, greater, null_ptr, 0) == bool_false
    && path_len(heap, less, null_ptr) + path_len(heap, greater, null_ptr) = path_len(heap, list, iterator);
}


_Bool inv_check(abstract_heapt *heap) {
  return forall(heap, less, null_ptr, 0) == bool_true
    && forall (heap, greater, null_ptr, 0) == bool_false
    && path_len(heap, less, null_ptr) + path_len(heap, greater, null_ptr) = path_len(heap, list, iterator);
}
