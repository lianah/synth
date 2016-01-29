#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPREDS=1 and -DNSLACK=1

/**
   void foo (List list) {
       Iterator it = list.iterator(); 
       Assume(!is_null(heap, list));
       int m = it.next();
       while(it.hasNext()) {
       // INVARIANAT: is_path(heap, list, it) == bool_true &&
                      (!alias(heap, list, it) && m == max(heap, list, it));
         int current = next(heap, it);
         if (current > m) {
           m = current; 
         }
       }
       Assert (is_path(heap, list, null_ptr) == bool_true &&
               m == max(heap, list, null_ptr));
   }
 **/

ptr_t list = 1;
ptr_t it = 2;

word_t m, current; 

void init_predicates() {
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
    if (current > m) {
      m = current; 
    }
}

_Bool assertion(abstract_heapt *heap) {
  return is_path(heap, list, null_ptr) == bool_true &&
    m == max(heap, list, null_ptr);
}

_Bool inv_check(abstract_heapt *heap) {
  return is_path(heap, list, it) == bool_true &&
    (!alias(heap, list, it) && m == max(heap, list, it));
}

_Bool inv_assume(abstract_heapt *heap) {
  return is_path(heap, list, it) == bool_true &&
    (!alias(heap, list, it) && m == max(heap, list, it));
}
