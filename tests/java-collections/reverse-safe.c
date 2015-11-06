#include "abstract_heap.h"

// Run with -DNPROG=4 and -DNPRED=1

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
  /* iterator(heap, it, list); */
  /* iterator(heap, it2, reversed); */
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
  //addI(heap, it2, current);
  assume(!is_null(heap, it2));
  iterator(heap, it2, reversed);
}

_Bool assertion(abstract_heapt *heap) {
  return 1;
  /* return path_len(heap, list, null_ptr) == path_len(heap, reversed, null_ptr) && */
  /*   forall(heap, list, null_ptr, 0) == forall(heap, reversed, null_ptr, 0) && */
  /*   exists(heap, list, null_ptr, 0) == exists(heap, reversed, null_ptr, 0); */
}

_Bool inv(abstract_heapt *heap) {
	 //assume(!is_null(heap, reversed));
  /* assume(!is_null(heap, it)); */
  // AAAAAAAAAAAAAA
  // THIS IS INCONSISTENT FOR UNKNOWN REASONS!!!!!!!!!!!!!!!!!!
   assume(is_path(heap, list, it));
   assume(is_path(heap, reversed, null_ptr));
   assume(!is_null(heap, it2));
   assume(path_len(heap, reversed, null_ptr) == path_len(heap, list, it));
   assume(alias(heap, it2, reversed));
  /* assume(alias(heap, it2, reversed)); */
  /* assume(path_len(heap, reversed, null_ptr) == path_len(heap, list, it)); */
  /* assert(alias(heap, reversed, null_ptr)); */
    //assert(alias(heap, list, it));
  
   return 1; //path_len(heap, reversed, null_ptr) == path_len(heap, list, it) && 
    //     forall(heap, list, it, 0) == forall(heap, reversed, null_ptr, 0) &&  
    /* exists(heap, list, it, 0) == exists(heap, reversed, null_ptr, 0) &&   */
    //alias(heap, it2, reversed);
}
