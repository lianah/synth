#include "abstract_heap.h"

// Run with -DNPROG=3

/*public static int min(int... array) {
    checkArgument(array.length > 0);
    int min = array[0];
    for (int i = 1; i < array.length; i++) {
      if (array[i] < min) {
        min = array[i];
      }
    }
    return min;
  }*/

ptr_t list = 1;
ptr_t it=2;

data_t result_min;
index_t i;

_Bool nothing (data_t val) { return 1; }
void init_predicates() {
  predicates[0] = nothing;
}

void init_heap(abstract_heapt *heap) {
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
}

void pre(abstract_heapt *heap) {
  Assume(!is_null(heap, list)); // Is not null (and hence not empty)
  result_min = getP(heap, list, 0);
  i = 1;
}

_Bool cond(abstract_heapt *heap) {
  return i < size(heap, list);
}

void body(abstract_heapt *heap) {
  if (getP(heap, list, i) < result_min) {
    result_min=getP(heap, list, i);
  }
  i++;
}

_Bool assertion(abstract_heapt *heap) {
  return is_path(heap, list, null_ptr) && result_min == min(heap, list, null_ptr);
}

_Bool inv_check(abstract_heapt *heap) {
  listIterator(heap, it, list, i);
  return !alias(heap, list, it) && result_min == min(heap, list, it);
}

_Bool inv_assume(abstract_heapt *heap) {
  listIterator(heap, it, list, i);
  return !alias(heap, list, it) && result_min == min(heap, list, it);
}
