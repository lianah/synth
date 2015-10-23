#include "abstract_heap.h"

ptr_t x = 1;
ptr_t y = 2;
ptr_t tmp = 3;

void pre(abstract_heapt *heap) {
  assume (!is_null(heap, x) &&
	  alias(heap, x, tmp));
}

void post(abstract_heapt *heap) {
  abstract_update(heap, tmp, y);
}


_Bool cond(const abstract_heapt *heap) {
  return path_len(heap, tmp, null_ptr) > 1;
}

void body(abstract_heapt *heap) {
  abstract_lookup(heap, tmp, tmp);
}

// LSH fixme: shouldn't this be something like:
// is_path(heap, x, y)
_Bool assertion(const abstract_heapt *heap) {
  return is_path(heap, x, tmp);
}

_Bool inv(const abstract_heapt *heap) {
  return !is_null(heap, tmp) && is_path(heap, x, tmp);
}
