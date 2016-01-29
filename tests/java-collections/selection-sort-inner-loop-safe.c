/*

int selection(List list) {
  Assume(!is_null(heap, list));
  ListIterator<Integer> it = list.listIterator();
  Integer min = it.next();
  while(it.hasNext()) {
    //Inv: is_path(heap, list, it) == bool_true &&
          (!alias(heap, list, it) && m == min(heap, list, it))
    Integer current = it.next();
    if (current < min) {
	min = current;
    }
  }
  Assert (is_path(heap, list, null_ptr) == bool_true &&
          (alias(heap, list, null_ptr) || m == min(heap, list, null_ptr)));
  return min;
}
*/

#include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPREDS=1 and -DNSLACK=1

ptr_t list = 1;
ptr_t it = 2;

word_t m, current; 

_Bool nothing (data_t val) { return 1; }
void init_predicates() {
  predicates[0] = nothing;
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
  /* dump_heap(heap, "heap1", "list it"); */
  /* printf("whole heap min = %d\n", min(heap, list, null_ptr)); */
  /* printf("it heap min = %d\n", min(heap, list, it)); */
  current = next(heap, it);
  /* printf("current = %d\n", current); */
  /* dump_heap(heap, "heap2", "list it");     */
  /* printf("min = %d\n", m); */
  if (current < m) {
    m = current; 
  }
  /* printf("min after = %d\n", m); */
}

_Bool assertion(abstract_heapt *heap) {
  return is_path(heap, list, null_ptr) == bool_true &&
    (alias(heap, list, null_ptr) || m == min(heap, list, null_ptr));
}

_Bool inv_check(abstract_heapt *heap) {
  return is_path(heap, list, it) == bool_true &&
    (!alias(heap, list, it) && m == min(heap, list, it));
}

_Bool inv_assume(abstract_heapt *heap) {
  return is_path(heap, list, it) == bool_true &&
    (!alias(heap, list, it) && m == min(heap, list, it));
}
