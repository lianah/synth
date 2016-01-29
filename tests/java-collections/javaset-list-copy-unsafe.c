/** 

  void foo(List list) {
    Set s = new HashSet();
    ListIterator it = list.listIterator();

    while(it.hasNext()) {
      // Invariant: s.size() <= path_len(list, it)
      int current = it.next();
      s.add(current);
    }
    Assert (s.size() == list.size());
  }
**/

#include "abstract_heap.h"

// Run with -DNPROG=3 -DNSETPROG=2 -DNPREDS=1 -DNSLACK=2

ptr_t list = 1;
ptr_t it = 2;

ptr_t set = 1;

data_t current; 


void pre(abstract_heapt *heap) {
  Assume (! empty(heap, list));
  set_abstract_new(heap, set);
  iterator(heap, it, list);
}

// LSH: is this ok with relational predicates?
_Bool pred(data_t val) {
  return val == current;
}

void init_predicates() {
  // initialize predicates
  predicates[0] = pred;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it);
}

void body(abstract_heapt *heap) {
  current = next(heap, it);
  set_add(heap, set, current, 0);
}

_Bool assertion(abstract_heapt *heap) {
  return path_len(heap, list, null_ptr) == set_size(heap, set);
}

_Bool inv_assume(abstract_heapt *heap) {
  return path_len(heap, list, it) >= set_size(heap, set) &&
    is_path(heap, list, it);
}

_Bool inv_check(abstract_heapt *heap) {
  return path_len(heap, list, it) >= set_size(heap, set) &&
    is_path(heap, list, it);
}

