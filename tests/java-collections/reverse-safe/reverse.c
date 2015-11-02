#include "abstract_heap.h"

ptr_t root = 1;
ptr_t new_root = 2;
ptr_t next = 3;

void pre(abstract_heapt *heap) {
  assume(is_null(heap, new_root) &&
	 !is_null(heap, root) &&
	 path_len(heap, root, null_ptr) == 7);
}

_Bool cond(abstract_heapt *heap) {
  return !is_null(heap, root);
}

void body(abstract_heapt *pre) {
  // next = root->next; 
  abstract_lookup(pre, next, root);
  // root->next = new_root
  abstract_update(pre, root, new_root);
  // new_root = root
  abstract_assign(pre, new_root, root);
  // root = next
  abstract_assign(pre, root, next);
}

_Bool assertion(abstract_heapt *heap) {
  return  path_len(heap, new_root, null_ptr) == 7;
}


_Bool inv(abstract_heapt *heap) {
  return path_len(heap, new_root, null_ptr) + path_len(heap, root, null_ptr) == 7 &&
         !alias(heap, root, new_root) &&
         ( !is_path(heap, new_root, root) || is_null(heap, root)) &&
         ( !is_path(heap, root, new_root) || is_null(heap, new_root)); 
  /* return alias(heap, root, next) && */
  /*   !alias(heap, root, new_root) && */
  /*   (!is_path(heap, root, new_root) || */
  /*    is_null(heap, new_root)) && */
  /*   ( !is_path(heap, new_root, root) || */
  /*     is_null(heap, root)); */
}
