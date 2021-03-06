/** 

  Set s = new HashSet();
  s.add(4);
  s.add(4);
  s.remove(4);
  Assert (s.size() == 1);
  
**/

#include "abstract_heap.h"

// Run with -DNPROG=1 -DNPREDS=2 -DNSETPROG=2

ptr_t set = 1;

void pre(abstract_heapt *heap) {
  set_abstract_new(heap, set);
  set_add(heap, set, 4, 0);
  set_add(heap, set, 4, 1);
  set_remove(heap, set, 4, 0);
}

_Bool isNotFour(data_t val) {
  return val != 4;
}

void init_predicates() {
  predicates[0] = isNotFour;
}

void init_heap(abstract_heapt *heap) {
}

_Bool cond(abstract_heapt *heap) {
  return 0; 
}

void body(abstract_heapt *heap) {
}

_Bool assertion(abstract_heapt *heap) {
  return set_size(heap, set) == 1;
}

_Bool inv_check(abstract_heapt *heap) {
  return set_size(heap, set) == 1;
}

_Bool inv_assume(abstract_heapt *heap) {
  return set_size(heap, set) == 1;
}


/** 

  Set s = new HashSet();
  s.add(x);
  s.add(y);

  s.remove(x);
  
  if (s.empty()) {
     Assert (x == y); 
  } else {
    Assert (s.size() == 1);
  }
  
**/


