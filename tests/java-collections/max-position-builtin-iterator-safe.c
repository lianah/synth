#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPREDS=1 and -DNSLACK=1

/**
  void foo (List lit) {
  Assume(!is_null(heap, list));
  int m = list.get(0);
  int idx = 1;
  while (idx < list.size()) {
    // INVARIANT: idx <= size(heap, list) && idx > 0 &&
    //             m == max(heap, list, it)
    int current = getP(heap, list, idx);
    if (current > m) {
      m = current; 
    }
    idx++;
  }
  Assert(is_path(heap, list, null_ptr) == bool_true &&
         m == max(heap, list, null_ptr););
   }
 **/

ptr_t list = 1;
ptr_t it = 2;

word_t m, current; 

index_t idx;

void init_predicates() {
}


void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
}

void pre(abstract_heapt *heap) {
  Assume(!is_null(heap, list));
  m = getP(heap, list, 0);
  idx = 1;
}

_Bool cond(abstract_heapt *heap) {
  return idx < size(heap, list);
}

void body(abstract_heapt *heap) {

    current = getP(heap, list, idx);
    if (current > m) {
      m = current; 
    }

    idx++;
}

_Bool assertion(abstract_heapt *heap) {
  return is_path(heap, list, null_ptr) == bool_true &&
    m == max(heap, list, null_ptr);
}

_Bool inv_check(abstract_heapt *heap) {
  listIterator(heap, it, list, idx);

  return idx <= size(heap, list) &&
    idx > 0 &&
    m == max(heap, list, it);
}

_Bool inv_assume(abstract_heapt *heap) {
  return inv_check(heap);
}
