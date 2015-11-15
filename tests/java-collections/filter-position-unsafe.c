#include "abstract_heap.h"

// Run with -DNPROG=3 -DNPREDS=2 -DNSLACK=2

ptr_t list = 1;
ptr_t it = 2;

data_t current;

index_t idx;

_Bool isLess(data_t val) {
  return val < 10;
}

_Bool isGreater(data_t val) {
  return val > 10;
}


void init_predicates() {  
  predicates[0] = isLess;
  predicates[1] = isGreater;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
  idx = nondet();
}


void pre(abstract_heapt *heap) {
  idx = 0;
}

_Bool cond(abstract_heapt *heap) {
  return idx < size(heap, list);
}

void body(abstract_heapt *heap) {
  //dump_heap(heap, "body.png", "list it");
  current = getP(heap, list, idx);
  if (isLess(current)) {
    removeP(heap, list, idx);
    //dump_heap(heap, "remove.png", "list it");
  }  else {
    idx++;
  }
}

_Bool assertion(abstract_heapt *heap) {
  dump_heap(heap, "assertion", "list it");
  return forall(heap, list, null_ptr, 1) == bool_true;
}

_Bool inv_assume(abstract_heapt *heap) {
  if (idx <= size(heap, list)) {
    listIterator(heap, it, list, idx);
    return forall_assume(heap, list, it, 1);
  } else {
    return 0;
  }
}


_Bool inv_check(abstract_heapt *heap) {
  return inv_assume(heap);
}
