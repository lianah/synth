#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPRED=1


ptr_t list = 1;
ptr_t iterator = 2;

_Bool isFour(data_t val) {
  return val == 4;
}

void init_predicates() {
  predicates[0] = isFour;
}

void pre(abstract_heapt *heap) {
  // LSH FIXME: make special transformer?
  //ListIterator<Int> iterator = list.listIterator()
  assign(heap, iterator, list);
}

_Bool cond(abstract_heapt *heap) {
  return has_next(heap, iterator);
}

void body(abstract_heapt *heap) {
  // iterator.set(4);
  set(heap, iterator, 4);
  // iterator.next();
  next(heap, iterator);
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, list, null_ptr, 0) == bool_true;
}

_Bool inv(abstract_heapt *heap) {
  return forall(heap, list, iterator, 0) == bool_true;
  // LSH: ORDER MATTERS:
  // if forall is before disjunction, transformer assert fails?
}
