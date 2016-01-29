#include "abstract_heap.h"

// Run with -DNPROG=5 -DNPREDS=2 -DNSLACK=2

/**
   void foo (List list) {
   Assume(empty(heap, less));
   Assume(empty(heap, greater));
   int idx = 0;
   while (idx < size(heap, list)) {
   // INVARIANT: forall_assume(heap, less, null_ptr, 0)
    && forall_assume (heap, greater, null_ptr, 1)
    && s_add(path_len(heap, less, null_ptr), path_len(heap, greater, null_ptr)) == idx
    && idx <= size(heap, list)
    int current = list.get(idx); 
    if (isLess(current)) {
      less.add(current);
    } else {
      greater.add(current);
    }
   idx++;
   }
   Assert (forall(heap, less, null_ptr, 0) == bool_true
   && forall (heap, greater, null_ptr, 1) == bool_true
   && s_add(path_len(heap, less, null_ptr),
	     path_len(heap, greater, null_ptr)) == path_len(heap, list, null_ptr));
   }
 **/

ptr_t list = 1;
ptr_t less = 2;
ptr_t greater = 3;

data_t current;
data_t pivot;

index_t idx;

_Bool isLess(data_t val) {
  return val < pivot ;
}

_Bool isGreater(data_t val) {
  return val >= pivot ;
}


void init_predicates() {  
  predicates[0] = isLess;
  predicates[1] = isGreater;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[less] = 0;
  heap->is_iterator[greater] = 0;
  idx = nondet();
}


void pre(abstract_heapt *heap) {
  Assume(empty(heap, less));
  Assume(empty(heap, greater));
  idx = 0;
}

_Bool cond(abstract_heapt *heap) {
  return idx < size(heap, list);
}

void body(abstract_heapt *heap) {
  dump_heap(heap, "body.png", "list less greater");
  current = getP(heap, list, idx);
  dump_heap(heap, "next.png", "list less greater");
  if (isLess(current)) {
    add(heap, less, current);
    dump_heap(heap, "less.png", "list less greater");
  } else {
    add(heap, greater, current);
    dump_heap(heap, "greater.png", "list less greater");
  }
  idx++;
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, less, null_ptr, 0) == bool_true
    && forall (heap, greater, null_ptr, 1) == bool_true
    && s_add(path_len(heap, less, null_ptr),
	     path_len(heap, greater, null_ptr)) == path_len(heap, list, null_ptr);
}

_Bool inv_assume(abstract_heapt *heap) {
  return forall_assume(heap, less, null_ptr, 0)
    && forall_assume (heap, greater, null_ptr, 1)
    && s_add(path_len(heap, less, null_ptr),
	     path_len(heap, greater, null_ptr)) == idx
    && idx <= size(heap, list);
}


_Bool inv_check(abstract_heapt *heap) {
  return inv_assume(heap);
}
