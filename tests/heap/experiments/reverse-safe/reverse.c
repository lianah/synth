#include "abstract_heap.h"

ptr_t root = 1;
ptr_t new_root = 2;
ptr_t next = 3;

void pre(abstract_heapt *heap) {
  assume(is_null(heap, new_root) &&
	 !is_null(heap, root) &&
	 is_path(heap, root, null_ptr) &&
	 alias(heap, root, next) &&
	 !alias(heap, root, new_root));
}

_Bool cond(abstract_heapt *heap) {
  return !is_null(heap, root);
}

void body(abstract_heapt *pre) {
  /* if (is_null(pre, root)) { */
  /*   return 0; */
  /* } */

  // next = root->next; 
  abstract_lookup(pre, next, root);

  /* if (is_null(&t1, root)) { */
  /*   return 0; */
  /* } */

  // root->next = new_root
  abstract_update(pre, root, new_root);
  // new_root = root
  abstract_assign(pre, new_root, root);
  // root = next
  abstract_assign(pre, root, next);
}

_Bool assertion(abstract_heapt *heap) {
  return  is_path(heap, new_root, null_ptr);
}


// can we express an invariant strong enough? seems like you need to talk about the
// annonymous sharing point (see counter-example)
_Bool inv(abstract_heapt *heap) {
  return is_path(heap, new_root, null_ptr)  && 
    alias(heap, root, next) &&
    !alias(heap, root, new_root) &&
    is_path(heap, root, null_ptr) &&
    ( !is_path(heap, new_root, root) ||
      is_null(heap, root));
}
