/*
ListIterator<Integer> it = list.listIterator();
Integer min = it.next();

while(it.hasNext()) {
    //Inv: forall(list,i,min <=v) && exists(list,i, min == v)
    
    Integer current = it.next();
    if (current < min) {
	min = current;
    }
}

//assert(forall(list,n,min <= v) && exists(list,n,min == v));
*/

#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPREDS=1 and -DNSLACK=1

ptr_t list = 1;
ptr_t it = 2;

word_t m, current; 

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
  Assume(!is_null(heap, list));
  m = next(heap, it);
}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it);
}

void body(abstract_heapt *heap) {

    current = next(heap, it);
    if (current < m) {
      // BUG (erroneous increment by 1)
      m = current+1; 
    }

}

_Bool assertion(abstract_heapt *heap) {
  return is_path(heap, list, null_ptr) == bool_true &&
    m == min(heap, list, null_ptr);
}

_Bool inv_check(abstract_heapt *heap) {
  return is_path(heap, list, it) == bool_true &&
    !alias(heap, list, it) && m == min(heap, list, it);
}

_Bool inv_assume(abstract_heapt *heap) {
  return is_path(heap, list, it) == bool_true &&
    !alias(heap, list, it) && m == min(heap, list, it);
}
