/*
  private static void sort(List<Integer> list) {
    int min, temp;
    int n;

    for (int j = 0; j < list.size()-1; j++) {
       //Inv: sorted(list,j,_,max1) && max1 <= min1 && forall(j+1,n,min1<=v) && exists(j+1,n,min1)

  	min = j;
  	for (int i = j+1; i < n; i++) {

	// Inv: forall(j+1,i,min<=v) && exists(j+1,i,min)
  	    if (list.get(i) < list.get(min)) {
  		min = i;
  	    }
  	}
  	temp = list.get(j);
  	list.set(j, list.get(min));
  	list.set(min, temp);
    }
  }

*/

#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPREDS=1 and -DNSLACK=1

ptr_t list = 1;
ptr_t it = 2;

word_t curr_min; 

_Bool nothing (data_t val) { return 1; }
void init_predicates() {
  predicates[0] = nothing;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
}

void pre(abstract_heapt *heap) {
  iterator(heap, it, list);
}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it);
}

void body(abstract_heapt *heap) {
  // We must have alias(heap, list, it) || max(heap, list, it) <= curr_min;

  // Inner loop invariant
  Assume(alias(heap, it, null_ptr) || curr_min == min(heap, it, null_ptr));

  addI(heap, list, it, curr_min);
}

_Bool assertion(abstract_heapt *heap) {
  return is_path(heap, list, null_ptr) == bool_true && 
    sorted(heap, list, null_ptr) == bool_true;
}

_Bool inv_check(abstract_heapt *heap) {
  return is_path(heap, list, it) == bool_true &&
    (alias(heap, list, it) ||
     (sorted(heap, list, it) == bool_true && 
      (alias(heap, it, null_ptr) || max(heap, list, it) <= min(heap, it, null_ptr))));
}

_Bool inv_assume(abstract_heapt *heap) {
  return is_path(heap, list, it) == bool_true &&
    (alias(heap, list, it) ||
     (sorted(heap, list, it) == bool_true && 
      (alias(heap, it, null_ptr) || max(heap, list, it) <= min(heap, it, null_ptr))));
}
