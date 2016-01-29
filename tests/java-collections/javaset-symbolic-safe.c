/** 

  void foo(int x, int y) {
    Set s = new HashSet();
    s.add(x);
    s.add(y);
    Assert (s.size() >= 1);
  }
**/

#include "abstract_heap.h"

// Run with -DNPROG=1 -DNPREDS=2 -DNSETPROG=2

ptr_t set = 1;
word_t x;
word_t y;

void pre(abstract_heapt *heap) {
  set_abstract_new(heap, set);
  set_add(heap, set, x, 0);
  set_add(heap, set, y, 1);
}

_Bool isNotX(data_t val) {
  return val != x;
}

_Bool isNotY(data_t val) {
  return val != y;
}

void init_predicates() {
  predicates[0] = isNotX;
  predicates[1] = isNotY;
}

void init_heap(abstract_heapt *heap) {
}

_Bool cond(abstract_heapt *heap) {
  return 0; 
}

void body(abstract_heapt *heap) {
}

_Bool assertion(abstract_heapt *heap) {
  return set_size(heap, set) >= 1;
}

_Bool inv_check(abstract_heapt *heap) {
  return set_size(heap, set) >= 1;
}

_Bool inv_assume(abstract_heapt *heap) {
  return set_size(heap, set) >= 1;
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


