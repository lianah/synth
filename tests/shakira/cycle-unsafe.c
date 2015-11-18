#include "abstract_heap.h"

// Run with -DNPROG=2 -DNPREDS=1 -DNSLACK=1

ptr_t list = 1;
ptr_t it = 2;
word_t idx;

void pre(abstract_heapt *heap) {
  Assume(size(heap, list) > 1);
  listIterator(heap, it, list, s_sub(size(heap, list), 1));
  Assume (forall_assume(heap, list, it, 0));
  idx = nondet_word_t();
  Assume(0 <= idx && idx < size(heap, list));
}

_Bool is0(data_t val) {
  return val == 0;
}



void init_predicates() {
  // initialize predicates
  predicates[0] = is0;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
}

_Bool cond(abstract_heapt *heap) {
  return 0;
}

void body(abstract_heapt *heap) {
}

_Bool assertion(abstract_heapt *heap) {
  return 0 == getP(heap, list, idx);
  //return getP(heap, list, idx) == 0;
}

_Bool inv_assume(abstract_heapt *heap) {
  if (size(heap, list) == 0)
    return 0;
  if ((0 <= idx) && (idx < size(heap, list))) {

    listIterator(heap, it, list, s_sub(size(heap, list), 1));
    printf("Index idx = %d\n", idx);
    dump_heap(heap, "assume", "list it");
    if (!forall_assume(heap, list, it, 0))
      return 0;

  } else {
    return 0;
  }
}
  
_Bool inv_check(abstract_heapt *heap) {
  return 1;
}
