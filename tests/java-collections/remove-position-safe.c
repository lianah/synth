#include "abstract_heap.h"

// Run with -DNPROG=3 -DNPREDS=1 -DNSLACK=2

/*
	List<Integer> data = new ArrayList<>();

  	int i = 0;
	while (i < data.size()) {
	    if (data.get(i) < 0) {
		data.remove(i);
	    } else {
		i++;
	    }
	}
*/

ptr_t list = 1;
ptr_t it = 2;

data_t current; 
word_t i;


void pre(abstract_heapt *heap) {
  Assume(size(heap, list) > 0);
  i = 0;
}

_Bool pred(data_t val) {
  return val >= 10;
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
  return  i < size(heap, list);
}

void body(abstract_heapt *heap) {
  //printf("Index i=%d\n", i);
  dump_heap(heap, "body", "list it");
  current = getP(heap, list, i);
  dump_heap(heap, "getP", "list it");
  if (!pred(current)) {
    removeP(heap, list, i);
    dump_heap(heap, "removeP", "list it");
  } else {
    i = i + 1;
  }
}

_Bool assertion(abstract_heapt *heap) {
   return forall(heap, list, null_ptr, 0);
}

_Bool inv_assume(abstract_heapt *heap) {
  if (0 <= i && i <= size(heap, list)) {
    listIterator(heap, it, list, i);
    //printf("Index i=%d\n", i);
    dump_heap(heap, "inv_assume", "list it");
    return forall_assume(heap, list, it, 0);
  } else
    return 0;
}

_Bool inv_check(abstract_heapt *heap) {
  if (0 <= i && i <= size(heap, list)) {
    listIterator(heap, it, list, i);
    //printf("Index i=%d\n", i);
    dump_heap(heap, "inv_check", "list it");
    return forall(heap, list, it, 0) == bool_true;
  } else
    return 0;
}
