#include "abstract_heap.h"

ptr_t x = 1;
ptr_t y = 2;
ptr_t tmpx = 3;
ptr_t tmpy = 4;
ptr_t cell = 5;

void pre(abstract_heapt *heap) {
  assume (! is_null(heap, x)
	  && is_path(heap, x, null_ptr)
	  && is_null(heap, y)
	  && is_null(heap, tmpx)
	  && is_null(heap, tmpy)
	  && is_null(heap, cell));

  // y = new ()
  abstract_new(heap, y);
  // tmpx = x-> next
  // abstract_lookup(heap, tmpx, x);
  // tmpy = y
  abstract_assign(heap, tmpy, y);
}

_Bool cond(abstract_heapt *heap) {
  return !is_null(heap, tmpx);
}

void body(abstract_heapt *heap) {
  // cell = new ()
  abstract_new(heap, cell);
  // tmpy->next = cell
  abstract_update(heap, tmpy, cell);
  // tmpy = tmpy->next
  abstract_lookup(heap, tmpy, tmpy);
  // tmpx = tmpx->next
  abstract_lookup(heap, tmpx, tmpx);
}

_Bool assertion(abstract_heapt *heap) {
  return path_len(heap, y, null_ptr) == path_len(heap, x, null_ptr);
}

_Bool inv(abstract_heapt *heap) {
  return path_len(heap, y, null_ptr) + path_len(heap, tmpx, null_ptr) == path_len(heap, x, null_ptr)
    && is_path(heap, x, tmpx)
    && is_path(heap, y, tmpy)
    && path_len(heap, tmpy, null_ptr) == 1;
}
