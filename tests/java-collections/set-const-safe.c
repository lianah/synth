#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPRED=1


ptr_t list = 1;
ptr_t it = 2;

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
  iterator(heap, it, list);
}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it);
}

void body(abstract_heapt *heap) {
  // it.next();
  next(heap, it);
  // it.set(4);
  setI(heap, it, 4);
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, list, null_ptr, 0) == bool_true;
}

_Bool inv(abstract_heapt *heap) {
  return //is_path(heap, list, it) &&
         forall(heap, list, it, 0) == bool_true;
  // LSH: ORDER MATTERS:
  // if forall is before disjunction, transformer assert fails?
}
