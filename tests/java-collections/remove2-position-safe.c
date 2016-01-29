#include "abstract_heap.h"

// Run with -DNPROG=2 -DNPRED=1 -DNSLACK=1

/*
  void foo (List list, int k ) {
    int init_size = list.size();
    init_k = k;
    Assume(list.size() > k);
    Assume( k >= 0);
    while (k >= 0) {
       // INVARIANT: s_add(s_sub(init_k, k), size(heap, list)) == init_size
       list.remove(0);
       k = k - 1;
    }
    Assert (size(heap, list) == s_sub(init_size, init_k));
    return list;
  }
*/

ptr_t list = 1;
//ptr_t it = 2;

word_t k;
word_t init_k;
word_t init_size;

void pre(abstract_heapt *heap) {
  k = nondet_word_t();
  init_size = size(heap, list);
  init_k = k;
  Assume(size(heap, list) > k);
  Assume( k >= 0);
}

_Bool pred(data_t val) {
  return val == 0;
}

void init_predicates() {
  predicates[0] = pred;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[list] = 0;
}

_Bool cond(abstract_heapt *heap) {
  return k > 0;
}

void body(abstract_heapt *heap) {
  dump_heap(heap, "body", "list");
  removeP(heap, list, 0);
  k = k - 1;
}

_Bool assertion(abstract_heapt *heap) {
  dump_heap(heap, "assertion", "list");
  return size(heap, list) == s_sub(init_size, init_k);
}

_Bool inv_check(abstract_heapt *heap) {
  return s_add(s_sub(init_k, k), size(heap, list)) == init_size;
}

_Bool inv_assume(abstract_heapt *heap) {
  return s_add(s_sub(init_k, k), size(heap, list)) == init_size;
}
