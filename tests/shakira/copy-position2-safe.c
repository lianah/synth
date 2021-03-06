#include "abstract_heap.h"

// Run with -DNPROG=5 -DNPREDS=1 -DNSLACK=2

/*
        Assume(copy.size() == data.size());
	
	for (int i = 0; i < 10; ++i) {
	    copy.set(i, data.get(i));
	}


 */

ptr_t list = 1;
ptr_t copy = 2;
ptr_t it = 3;
ptr_t it2 = 4;

data_t current; 
word_t i;
word_t x;

void pre(abstract_heapt *heap) {
  Assume (! empty(heap, list));
  Assume (size(heap, copy) == size(heap, list));
  Assume(!alias(heap, list, copy));
  i = 0;
}

_Bool pred(data_t val) {
  // LSH: if we want to be fancy we can use UF to show it forall predicates
  return val == 0;
}

void init_predicates() {
  // initialize predicates
  predicates[0] = pred;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[copy] = 0;
  heap->is_iterator[it] = 1;
  heap->is_iterator[it2] = 1;
}

_Bool cond(abstract_heapt *heap) {
  return i < size(heap, list);
}

void body(abstract_heapt *heap) {
  current = getP(heap, list, i);
  setP(heap, copy, i, current);
  i = i + 1;
}

_Bool assertion(abstract_heapt *heap) {
  dump_heap(heap, "assertion", "list copy it");
  return ((forall(heap, list, null_ptr, 0) == bool_true &&
	   forall(heap, copy, null_ptr, 0) == bool_true) ||
	  (forall(heap, list, null_ptr, 0) == bool_false &&
	   forall(heap, copy, null_ptr, 0) == bool_false));
}

_Bool inv_assume(abstract_heapt *heap) {
  if (0 <= i && i <= size(heap, list)) {
    listIterator(heap, it, list, i);
    listIterator(heap, it2, copy, i);
    return
      size(heap, copy) == size(heap, list) &&
      forall_assume(heap, list, it, 0) == forall_assume(heap, copy, it2, 0);
  } else {
    return 0;
  }
}

_Bool inv_check(abstract_heapt *heap) {
  if (0 <= i && i <= size(heap, list)) {
    listIterator(heap, it, list, i);
    listIterator(heap, it2, copy, i);
    return
      size(heap, copy) == size(heap, list) &&
      ((forall(heap, list, it, 0) == bool_true &&
	forall(heap, copy, it2, 0) == bool_true) ||
       (forall(heap, list, it, 0) == bool_false &&
	forall(heap, copy, it2, 0) == bool_false));
  } else {
    return 0;
  }
}
