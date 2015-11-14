#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPRED=1

ptr_t list = 1;
ptr_t it = 2;

word_t idx;

_Bool isPos(data_t val) {
  return val > 10;
}

void init_predicates() {
  predicates[0] = isPos;
}

void init_heap(abstract_heapt *heap) {
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
}

void pre(abstract_heapt *heap) {
  idx = 0;
}

_Bool cond(abstract_heapt *heap) {
  printf("XXX idx: %d, size: %d", idx, size(heap, list));
  return idx < size(heap, list);
}

void body(abstract_heapt *heap) {
  word_t current = getP(heap, list, idx);
  if (current >= 0) {
    setP(heap, list, idx, 0);
  }
  idx++;
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, list, null_ptr, 0) == bool_true;
}

_Bool inv_assume(abstract_heapt *heap) {
  printf("XXX idx: %d, size: %d", idx, size(heap, list));
  iteratorP(heap, it, list, idx);
  return forall_assume(heap, list, it, 0) == bool_true;
} 


_Bool inv_check(abstract_heapt *heap) {
  printf("XXX idx: %d, size: %d", idx, size(heap, list));
  iteratorP(heap, it, list, idx);
  return forall(heap, list, it, 0) == bool_true;
}
