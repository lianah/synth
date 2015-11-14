#include "abstract_heap.h"

// Run with -DNPROG=5 -DNPREDS=1 -DNSLACK=2

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

_Bool nothing (data_t val) { return 1; }
void init_predicates() {
  predicates[0] = nothing;
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
  //printf("pivot = %d\n", pivot);
  //dump_heap(heap, "body", "list less greater it");
  current = next(heap, it);
  //printf("current = %d\n", current);
  //dump_heap(heap, "next", "list less greater it");
  if (isLess(current)) {
    add(heap, less, current);
    //dump_heap(heap, "less", "list less greater it");
  } else {
    add(heap, greater, current);
    //dump_heap(heap, "greater", "list less greater it");
  }
}

_Bool assertion(abstract_heapt *heap) {
  return (alias(heap, less, null_ptr) || max(heap, less, null_ptr) < pivot) &&
    (alias(heap, greater, null_ptr) || min(heap, greater, null_ptr) >= pivot);
}

_Bool inv_assume(abstract_heapt *heap) {
  return is_path(heap, list, it) && 
    ((is_null(heap, less) && is_null(heap, greater)) || !alias(heap, less, greater))  &&
    (alias(heap, less, it) || max(heap, less, it) < pivot) /* && */
    /* (alias(heap, greater, it) || min(heap, greater, it) >= pivot) */;
}


_Bool inv_check(abstract_heapt *heap) {
  // dump_heap(heap, "check", "list less greater it");

  return is_path(heap, list, it) &&
    ((is_null(heap, less) && is_null(heap, greater)) || !alias(heap, less, greater))  &&
    (alias(heap, less, it) || max(heap, less, it) < pivot) &&
    (alias(heap, greater, it) || min(heap, greater, it) >= pivot);
}
