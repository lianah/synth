#include "abstract_heap.h"
/**
   void foo(List list) {
   Iterator it = list.iterator();
   while (it.hasNext()) {
     // INVARIANT: forall(heap, list, it, 1) == bool_true
     current = next(heap, it);
     if (isLess(current)) {
        it.remove();
   }
   Assert(forall(heap, list, null_ptr, 1) == bool_true);
  }
 **/

// Run with -DNPROG=3 -DNPREDS=2 -DNSLACK=2

ptr_t list = 1;
ptr_t it = 2;

data_t current;

_Bool isLess(data_t val) {
  return val < 10;
}

_Bool isGreater(data_t val) {
  return val >= 10;
}


void init_predicates() {  
  predicates[0] = isLess;
  predicates[1] = isGreater;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
}


void pre(abstract_heapt *heap) {
  iterator(heap, it, list);
}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it);
}

void body(abstract_heapt *heap) {
  //dump_heap(heap, "body.png", "list it");
  current = next(heap, it);
  if (isLess(current)) {
    removeI(heap, it);
    //dump_heap(heap, "remove.png", "list it");
  } 
}

_Bool assertion(abstract_heapt *heap) {
  dump_heap(heap, "assertion", "list it");
  return forall(heap, list, null_ptr, 1) == bool_true;
}

_Bool inv_assume(abstract_heapt *heap) {
  return forall_assume(heap, list, it, 1);
}


_Bool inv_check(abstract_heapt *heap) {
  return forall(heap, list, it, 1) == bool_true;
}
