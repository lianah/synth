/** 

  void foo(int x, int y) {
    Set s = new HashSet();
    s.add(x);
    s.add(y);
    Assert (s.size() == 2);
  }
**/

#include "abstract_heap.h"

// Run with -DNPROG=1 -DNPREDS=2 -DNSETPROG=2

ptr_t set = 1;
word_t val_x;
word_t val_y;

void pre(abstract_heapt *heap) {
  set_abstract_new(heap, set);
  set_add(heap, set, val_x, 0);
  set_add(heap, set, val_y, 1);
}

_Bool isNotX(data_t val) {
  return val != val_x;
}

_Bool isNotY(data_t val) {
  return val != val_y;
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
  return set_size(heap, set) == 2;
}

_Bool inv_check(abstract_heapt *heap) {
  return set_size(heap, set) == 2;
}

_Bool inv_assume(abstract_heapt *heap) {
  return set_size(heap, set) == 2;
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


