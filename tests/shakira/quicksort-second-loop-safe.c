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
  // pick the pivot to be the first element in the list to be sorted
  iterator(heap, it, list);
  Assume(hasNext(heap, it));
  pivot = next(heap, it);

  // call partition (quicksort-first-loop-safe.c)
  // assume the postcond of partition 
  Assume((alias(heap, less, null_ptr) || max(heap, less, null_ptr) < pivot) &&
	 (alias(heap, greater, null_ptr) || min(heap, greater, null_ptr) >= pivot));
  // recursive call to quicksort 
  // assume the postcond of quicksort for the left partition (< pivot)
  Assume(alias(heap, less, null_ptr) || sorted(heap, less, null_ptr));
  // Postcond of quicksort for the right partition (>= pivot)
  Assume(alias(heap, greater, null_ptr) || sorted(heap, greater, null_ptr));

  // reuse iterator it to iterate over greater and copy its elements into less
  iterator(heap, it, greater);

}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it);
}

void body(abstract_heapt *heap) {
  /* if(path_len(heap, less, null_ptr) > 1) { */
  /*   printf("max less = %d\n", max(heap, less, null_ptr)); */
  /* } */
  /* else { */
  /*   printf("there is no max value for less-->null\n"); */
  /* } */
  /* dump_heap(heap, "body", "list less greater it"); */
  current = next(heap, it);
  /* printf("current = %d\n", current); */
  /* dump_heap(heap, "next", "list less greater it"); */
  add(heap, less, current);
  /* dump_heap(heap, "final", "list less greater it"); */
}

_Bool assertion(abstract_heapt *heap) {
  // less is sorted
  return alias(heap, less, null_ptr) || sorted(heap, less, null_ptr);
}

_Bool inv_assume(abstract_heapt *heap) {
  // max of less <= min of greater  &&
  // less is sorted &&
  // greater is sorted 
  return (alias(heap, less, null_ptr) || 
	  alias(heap, it, null_ptr) || 
	  max(heap, less, null_ptr) <= min(heap, it, null_ptr)) &&
    (alias(heap, less, null_ptr) || sorted(heap, less, null_ptr)) &&
    (alias(heap, it, null_ptr) || sorted(heap, it, null_ptr));
}


_Bool inv_check(abstract_heapt *heap) {
  return (alias(heap, less, null_ptr) || 
	  alias(heap, it, null_ptr) || 
	  max(heap, less, null_ptr) <= min(heap, it, null_ptr)) &&
    (alias(heap, less, null_ptr) || sorted(heap, less, null_ptr)) &&
    (alias(heap, it, null_ptr) || sorted(heap, it, null_ptr));
}
