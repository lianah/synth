#include "abstract_heap.h"

// Run with -DNPROG=3

/*    public static int hashCodeForList(final Collection<?> list) {
        if (list == null) {
            return 0;
        }
        int hashCode = 1;
        final Iterator<?> it = list.iterator();

        while (it.hasNext()) {
            final Object obj = it.next();
            hashCode = 31 * hashCode + (obj == null ? 0 : obj.hashCode());
        }
        return hashCode;
    }*/

ptr_t list1=1;
ptr_t list2=2;
ptr_t it1=3;
ptr_t it2=4;

data_t hashCode1;
data_t hashCode2;
data_t obj1;
data_t obj2;

_Bool nothing (data_t val) { return 1; }
void init_predicates() {
  predicates[0] = nothing;
}

void init_heap(abstract_heapt *heap) {
  heap->is_iterator[list] = 0;
  heap->is_iterator[it] = 1;
}

void pre(abstract_heapt *heap) {
  hashCode=1;
  iterator(heap, it, list);
}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it);
}

void body(abstract_heapt *heap) {
  obj=next(heap, it);
  hashCode=31 * hashCode + obj;
}

_Bool assertion(abstract_heapt *heap) {
  return is_path(heap, list, null_ptr) && result_max == max(heap, list, null_ptr);
}

_Bool inv_check(abstract_heapt *heap) {
  listIterator(heap, it, list, i);
  return !alias(heap, list, it) && result_max == max(heap, list, it);
}

_Bool inv_assume(abstract_heapt *heap) {
  listIterator(heap, it, list, i);
  return !alias(heap, list, it) && result_max == max(heap, list, it);
}
