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
  Assume(!is_null(heap, list));
}

_Bool cond(abstract_heapt *heap) {
  printf("XXX cond idx: %d, size: %d\n", idx, size(heap, list));
  return idx < size(heap, list);
}

void body(abstract_heapt *heap) {
  printf("BODY!!!!!\n");
  dump_heap(heap, "a", "list it");
  word_t current = getP(heap, list, idx);
  iteratorP(heap, it, list, idx);
  dump_heap(heap, "b", "list it");
  if (current >= 0) {
    setP(heap, list, idx, 0);
    dump_heap(heap, "c", "list it");
  }

  dump_heap(heap, "d", "list it");
  idx++;
  Assert(0, "do dooo doooooo do do");
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, list, null_ptr, 0) == bool_true;
}

_Bool inv_assume(abstract_heapt *heap) {
  printf("XXX invas idx: %d, size: %d\n", idx, size(heap, list));
  iteratorP(heap, it, list, idx);
  return !is_null(heap, list) && forall_assume(heap, list, it, 0) == bool_true;
} 


_Bool inv_check(abstract_heapt *heap) {
  printf("XXX invch idx: %d, size: %d\n", idx, size(heap, list));
  iteratorP(heap, it, list, idx);
  return !is_null(heap, list) && forall(heap, list, it, 0) == bool_true;
}
