#include "abstract_heap.h"

// Run with -DNPROG=5 -DNPREDS=1 -DNSLACK=1

/*
  
  ListIterator<Integer> it = data.listIterator();
  ListIterator<Integer> it2 = reversed.listIterator();
  while(it.hasNext()) {
    Integer current = it.next();
    it2.add(current);
    it2 = reversed.listIterator();
 }
*/

ptr_t list = 1;
ptr_t reversed = 2;
ptr_t it = 3;
ptr_t it2 = 4;

data_t current; 

void pre(abstract_heapt *heap) {
  assume(!empty(heap, list));
  assume(empty(heap, reversed));
  iterator(heap, it, list);
  iterator(heap, it2, reversed);
}

_Bool pred(data_t val) {
  // LSH: if we want to be fancy we can use UF to show it forall predicates
  return val == 0;
}

void init_predicates() {
  predicates[0] = pred;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[reversed] = 0;
  heap->is_iterator[it] = 1;
  heap->is_iterator[it2] = 1;
}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it);
}

void body(abstract_heapt *heap) {
  current = next(heap, it);
  addI(heap, it2, current);
  addI(heap, it2, current);
  iterator(heap, it2, reversed);
}

_Bool assertion(abstract_heapt *heap) {
   return path_len(heap, list, null_ptr) == path_len(heap, reversed, null_ptr) &&
    forall(heap, list, null_ptr, 0) == forall(heap, reversed, null_ptr, 0);
}

_Bool inv_assume(abstract_heapt *heap) {
   return path_len(heap, reversed, null_ptr) == path_len(heap, list, it) && 
     forall_assume(heap, list, it, 0) == forall_assume(heap, reversed, null_ptr, 0) &&  
     is_path(heap, list, it) &&
     alias(heap, it2, reversed) &&
     !alias(heap, list, reversed);
}


_Bool inv_check(abstract_heapt *heap) {
   return path_len(heap, reversed, null_ptr) == path_len(heap, list, it) && 
     forall(heap, list, it, 0) == forall(heap, reversed, null_ptr, 0) &&  
     is_path(heap, list, it) &&
     alias(heap, it2, reversed) &&
     !alias(heap, list, reversed);
}

