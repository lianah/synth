#include "abstract_heap.h"

// Run with -DNPROG=3 -DNPREDS=1


ptr_t list = 1;
ptr_t it = 2;

index_t idx;

_Bool isFour(data_t val) {
  return val == 4;
}

void init_predicates() {
  predicates[0] = isFour;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
}

void pre(abstract_heapt *heap) {
  //ListIt<Int> it = list.listIterator()
  //iterator(heap, it, list);
  idx = 0;
}

_Bool cond(abstract_heapt *heap) {
  return idx < size(heap, list);
}

void body(abstract_heapt *heap) {
  dump_heap(heap, "a", "list it");
  setP(heap, list, idx, 4);
  idx++;
  dump_heap(heap, "b", "list it");
  //Assert(0, "do dooo doo doo");
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, list, null_ptr, 0) == bool_true;
}

_Bool inv(abstract_heapt *heap) {
  iteratorP(heap, it, list, idx);
  return forall(heap, list, it, 0) == bool_true;
}
