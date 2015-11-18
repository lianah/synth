#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPRED=1

ptr_t list = 1;
ptr_t it = 2;

_Bool isPos(data_t val) {
  return val >= 0;
}

void init_heap(abstract_heapt *heap) {
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
}

void init_predicates() {  
  predicates[0] = isPos;
}

void pre(abstract_heapt *heap) {
  assign(heap, it, list);
}

_Bool cond(abstract_heapt *heap) {
  return has_next(heap, it);
}

void body(abstract_heapt *heap) {
  word_t current = get(heap, it);
  if (current < 0) {
    set(heap, it, 0);
  }
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, list, null_ptr, 0) == bool_true;
}

_Bool inv_assume(abstract_heapt *heap) {
  return forall_assume(heap, list, it, 0) == bool_true;
} 


_Bool inv_check(abstract_heapt *heap) {
  return forall(heap, list, it, 0) == bool_true;
} 
