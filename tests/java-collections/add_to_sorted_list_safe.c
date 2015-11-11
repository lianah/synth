#include "abstract_heap.h"

// Run with -DNPROG=2 and -DNPRED=0 and -DNSLACK=1

ptr_t list = 1;
ptr_t it = 2;

void pre(abstract_heapt *heap) {
  Assume (empty(heap, list));
  add(heap, list, 10);
  add(heap, list, 11);
}

void init_predicates() {}

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
  return sorted(heap, list, null_ptr);
}

_Bool inv_check(abstract_heapt *heap) {
  return sorted(heap, list, null_ptr) == bool_true;
}

_Bool inv_assume(abstract_heapt *heap) {
  return sorted(heap, list, null_ptr) == bool_true;
}
