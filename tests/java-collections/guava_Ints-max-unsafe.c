#include "abstract_heap.h"

// Run with -DNPROG=3

/*public static int max(int... array) {
    checkArgument(array.length > 0);
    int max = 0; // Error!
    for (int i = 1; i < array.length; i++) {
      if (array[i] > max) {
        max = array[i];
      }
    }
    return max;
  }*/

ptr_t list = 1;
ptr_t it=2;

data_t result_max;
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
  //result_max = getP(heap, list, 0); // Safe
  result_max = 0; // Unsafe!
  i = 1;
}

_Bool cond(abstract_heapt *heap) {
  return i < size(heap, list);
}

void body(abstract_heapt *heap) {
  if (getP(heap, list, i) > result_max) {
    result_max=getP(heap, list, i);
  }
  i++;
}

_Bool assertion(abstract_heapt *heap) {
  return is_path(heap, list, null_ptr) && result_max == max(heap, list, null_ptr);
}

_Bool inv_check(abstract_heapt *heap) {
  listIterator(heap, it, list, i);
  return !alias(heap, list, it) && result_max == max(heap, list, it);
}

_Bool inv_assume(abstract_heapt *heap) {
  listIterator(heap, it, list, i);
  return !alias(heap, list, it) && result_max == max(heap, list, it);
}
