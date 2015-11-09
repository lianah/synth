#include "abstract_heap.h"

// Run with -DNPROG=3 -DNPRED=1 

/*	ListIterator<Integer> it = data.listIterator();
	while(it.hasNext()) {
	    Integer current = it.next();
	    if (current != 0) {
		it.remove();
	    }
	}
*/

ptr_t list = 1;
ptr_t it = 2;

data_t current; 

void pre(abstract_heapt *heap) {
  iterator(heap, it, list);
}

_Bool pred(data_t val) {
  return val == 0;
}

void init_predicates() {
  predicates[0] = pred;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it);
}

void body(abstract_heapt *heap) {
  current = next(heap, it);
  if (current > 2) {
    removeI(heap, it);
  }
}

_Bool assertion(abstract_heapt *heap) {
   return forall(heap, list, null_ptr, 0);
}

_Bool inv(abstract_heapt *heap) {
   return forall(heap, list, it, 0);
}
