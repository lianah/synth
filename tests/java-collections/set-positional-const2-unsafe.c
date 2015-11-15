#include "abstract_heap.h"

// Run with -DNPROG=2 and -DNPRED=1

ptr_t list = 1;

word_t idx;

_Bool isPos(data_t val) {
  return val >= 0;
}

void init_predicates() {  
  predicates[0] = isPos;
}

void init_heap(abstract_heapt *heap) {
  heap->is_iterator[list] = 0;
}

void pre(abstract_heapt *heap) {
  idx = 0;
}

_Bool cond(abstract_heapt *heap) {
  return idx < size(heap, list);
}

void body(abstract_heapt *heap) {
  dump_heap(heap, "body, before get", "list");

  word_t current = getP(heap, list, idx);

  printf("XXX current = %d", current);

  if (current < 0) {
    setP(heap, list, idx, -1);
    dump_heap(heap, "body, after set", "list");
  }
  idx++;
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, list, null_ptr, 0) == bool_false;
}

_Bool inv_assume(abstract_heapt *heap) {
  return forall_assume(heap, list, iterator, 0) == bool_true;
} 


_Bool inv_check(abstract_heapt *heap) {
  return forall(heap, list, iterator, 0) == bool_true;
} 
