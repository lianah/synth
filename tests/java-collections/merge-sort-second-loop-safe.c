#include "abstract_heap.h"

/* -- start with two sorted lists a and c such that the elements in c are smaller than the elements in c
   -- copy the elements in a at the end of list c
   -- show that list c is sorted in the end
*/

// Run with -DNPROG=4 -DNPREDS=1 -DNSLACK=1

/**
   List merge(List a, List b) {
     int ia = 0;
     // assume the two input lists are sorted
     Assume(alias(heap, a, null_ptr) || sorted(heap, a, null_ptr));
     Assume(alias(heap, c, null_ptr) || sorted(heap, c, null_ptr));
     Assume(alias(heap, a, null_ptr) || 
            alias(heap, c, null_ptr) || 
	    max(heap, c, null_ptr) <= min(heap, a, null_ptr));
     while (0 <= ia && ia < a.size()) {
        // INVARIANT: (alias(heap, a, null_ptr) || sorted(heap, a, null_ptr)) &&
        //    (alias(heap, c, null_ptr) || sorted(heap, c, null_ptr)) && 
	//    (alias(heap, ita, null_ptr) || 
	//     alias(heap, c, null_ptr) || 
	//     max(heap, c, null_ptr) <= min(heap, ita, null_ptr))
        int currenta = a.get(ia);
	c.add(currenta);
     }
     Assert (alias(heap, c, null_ptr) || sorted(heap, c, null_ptr));
     return c;
     }
 **/

ptr_t a = 1;
ptr_t c = 2;
ptr_t ita = 3;

data_t ia;

data_t currenta;

_Bool nothing (data_t val) { return 1; }
void init_predicates() {
  predicates[0] = nothing;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[a] = 0;
  heap->is_iterator[c] = 0;
  heap->is_iterator[ita] = 1;
}

void pre(abstract_heapt *heap) {
  // initialise the index we use to iterate over the source list a
  ia = 0;
  
  // assume the two input lists are sorted
  Assume(alias(heap, a, null_ptr) || sorted(heap, a, null_ptr));
  Assume(alias(heap, c, null_ptr) || sorted(heap, c, null_ptr));

  // the elements in the destination list c are smaller than the elements
  // in the source list a
  Assume(alias(heap, a, null_ptr) || 
	 alias(heap, c, null_ptr) || 
	 max(heap, c, null_ptr) <= min(heap, a, null_ptr));

  dump_heap(heap, "pre", "a c ita");
}

_Bool cond(abstract_heapt *heap) {
  // we did not reach the end of the source list a
  return 0 <= ia && ia < size(heap, a);
}

void body(abstract_heapt *heap) {
  //dump_heap(heap, "body", "a c ita");
  // get the next element from a
  currenta = getP(heap, a, ia);

  //printf("add from list a element %d\n", currenta);

  // add it at the end of list c
  add(heap, c, currenta);

  //dump_heap(heap, "final", "a c ita");
}

_Bool assertion(abstract_heapt *heap) {
  // c is sorted
  return alias(heap, c, null_ptr) || sorted(heap, c, null_ptr);
}

_Bool inv_assume(abstract_heapt *heap) {
  listIterator(heap, ita, a, ia);

  // a is sorted and
  // c is sorted and 
  // the elements in c are all smaller than the elements in both a and b
  return (alias(heap, a, null_ptr) || sorted(heap, a, null_ptr)) &&
    (alias(heap, c, null_ptr) || sorted(heap, c, null_ptr)) && 
    (alias(heap, ita, null_ptr) || 
     alias(heap, c, null_ptr) || 
     max(heap, c, null_ptr) <= min(heap, ita, null_ptr));
}


_Bool inv_check(abstract_heapt *heap) {
  listIterator(heap, ita, a, ia);

  // a is sorted and
  // c is sorted and 
  // the elements in c are all smaller than the elements in both a and b
  return (alias(heap, a, null_ptr) || sorted(heap, a, null_ptr)) &&
    (alias(heap, c, null_ptr) || sorted(heap, c, null_ptr)) && 
    (alias(heap, ita, null_ptr) || 
     alias(heap, c, null_ptr) || 
     max(heap, c, null_ptr) <= min(heap, ita, null_ptr));
}
