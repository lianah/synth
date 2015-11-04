#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPRED=1

ptr_t list = 1;
ptr_t iterator = 2;

_Bool isPos(data_t val) {
  return val >= 0;
}

void init_predicates() {  
  predicates[0] = isPos;
}

void pre(abstract_heapt *heap) {
  assign(heap, iterator, list);
}

_Bool cond(abstract_heapt *heap) {
  return has_next(heap, iterator);
}

void body(abstract_heapt *heap) {
  current = get(heap, iterator);
  if (current < 0) {
    set(heap, iterator, 0);
  }
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, list, null_ptr, 0) == bool_true;
}

_Bool inv(abstract_heapt *heap) {
  return forall(heap, list, iterator, 0) == bool_true;
} 
