#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPRED=1

ptr_t list = 1;
ptr_t iterator = 2;

_Bool isPos(data_t val) {
  return val >= 0;
}

_Bool isZero(data_t val) {
  return val == 0;
}


void init_predicates() {  
  predicates[0] = isPos;
  predicates[1] = isZero;
}

void pre(abstract_heapt *heap) {
  exists(heap, list, null_ptr, 0 /*isPos*/);
  assign(heap, iterator, list);
}

_Bool cond(abstract_heapt *heap) {
  return has_next(heap, iterator);
}

void body(abstract_heapt *heap) {
  current = get(heap, iterator);
  if (isPos(current)) {
    set(heap, iterator, 0);
  }
}

_Bool assertion(abstract_heapt *heap) {
  return exists(heap, list, null_ptr, 1 /*isZero*/) == bool_true;
}

_Bool inv(abstract_heapt *heap) {
  return exists(heap, list, iterator, 1 /*isZero*/) == bool_true;
} 
