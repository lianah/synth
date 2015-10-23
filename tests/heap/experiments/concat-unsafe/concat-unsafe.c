#include "abstract_heap.h"

ptr_t x = 1;
ptr_t y = 2;
ptr_t tmp = 3;

/* int init(abstract_heapt *heap) { */
/*   return is_path(heap, x, null_ptr); */
/* } */

/* word_t rank1(abstract_heapt *heap) { */
/*   return path_len(heap, tmp, null_ptr); */
/* } */

/* word_t rank2(abstract_heapt *heap) { */
/*   return 1; */
/* } */

void pre(abstract_heapt *pre) {
  __CPROVER_assume(!is_null(pre, x) &&
         alias(pre, x, tmp));
}

_Bool cond(const abstract_heapt *heap) {
  return !is_null(heap, tmp);
}

void body(abstract_heapt *pre) {
  abstract_lookup(pre, tmp, tmp);
}

void post(abstract_heapt *heap) {
  abstract_update(heap, tmp, y);
}

_Bool assertion(abstract_heapt *heap) {
  return is_path(heap, x, tmp);
}

/* int danger(abstract_heapt *heap) { */
/*   return is_path(heap, tmp, null_ptr); */
/* } */

_Bool inv(const abstract_heapt *heap) {
  return !is_null(heap, tmp) && is_path(heap, x, tmp);
}
