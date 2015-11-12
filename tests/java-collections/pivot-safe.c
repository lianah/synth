#include "abstract_heap.h"

// Run with -DNPROG=5 -DNPREDS=2 -DNSLACK=2

ptr_t list = 1;
ptr_t less = 2;
ptr_t greater = 3;
ptr_t it = 4;

data_t current;
data_t pivot;

_Bool isLess(data_t val) {
  return val < pivot ;
}

_Bool isGreater(data_t val) {
  return val >= pivot ;
}


void init_predicates() {  
  predicates[0] = isLess;
  predicates[1] = isGreater;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[less] = 0;
  heap->is_iterator[greater] = 0;
  heap->is_iterator[it] = 1;
}


void pre(abstract_heapt *heap) {
  Assume(empty(heap, less));
  Assume(empty(heap, greater));
  iterator(heap, it, list);
}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it);
}

void body(abstract_heapt *heap) {
  current = next(heap, it);
  if (isLess(current)) {
    add(heap, less, current);
  } else {
    add(heap, greater, current);
  }
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, less, null_ptr, 0) == bool_true
    && forall (heap, greater, null_ptr, 1) == bool_true
    && path_len(heap, less, null_ptr) + path_len(heap, greater, null_ptr) == path_len(heap, list, null_ptr);
}

_Bool inv_assume(abstract_heapt *heap) {
  return forall_assume(heap, less, null_ptr, 0)
    && forall_assume (heap, greater, null_ptr, 1)
    && path_len(heap, less, null_ptr) + path_len(heap, greater, null_ptr) == path_len(heap, list, it);
}


_Bool inv_check(abstract_heapt *heap) {
  return forall(heap, less, null_ptr, 0) == bool_true
    && forall (heap, greater, null_ptr, 1) == bool_true 
    && path_len(heap, less, null_ptr) + path_len(heap, greater, null_ptr) == path_len(heap, list, it);
}
