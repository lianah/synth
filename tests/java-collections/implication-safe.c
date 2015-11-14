#include "abstract_heap.h"

// Run with -DNPROG=4 -DNPREDS=3

ptr_t list = 1;
ptr_t it1 = 2;
ptr_t it2 = 3;

_Bool isLess(data_t val) {
  return val <= 0 ;
}

_Bool isGreater(data_t val) {
  return val >= 0 ;
}

_Bool isEqual(data_t val) {
  return val != 0 ;
}


void init_predicates() {  
  predicates[0] = isLess;
  predicates[1] = isGreater;
  predicates[2] = isEqual;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[it1] = 0;
  heap->is_iterator[it2] = 0;
}


void pre(abstract_heapt *heap) {
  Assume(forall_assume(heap, list, it2, 0));
  Assume(forall_assume(heap, it1, null_ptr, 1));
  Assume(is_path(heap, it1, it2) &&
	 is_path(heap, list, it1) &&
	 path_len(heap, it1, it2) > 1);
}

_Bool cond(abstract_heapt *heap) {
  return 0;
}

void body(abstract_heapt *heap) {
}

_Bool assertion(abstract_heapt *heap) {
  /* exists x between it1 and it2 that is equal to 0*/
  return forall(heap, it1, it2, 2) == bool_false;
}

_Bool inv_assume(abstract_heapt *heap) {
  return
       forall(heap, list, it2, 0) == bool_true
    && forall(heap, it1, null_ptr, 1) == bool_true
    && is_path(heap, it1, it2)
    && is_path(heap, list, it1)
    && path_len(heap, it1, it2) > 1;
}

_Bool inv_check(abstract_heapt *heap) {
  return 1;
}
