#include "abstract_heap.h"

// Run with -DNPROG=5

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
  heap->is_iterator[list1] = 0;
  heap->is_iterator[list2] = 0;
  heap->is_iterator[it1] = 1;
  heap->is_iterator[it2] = 1;
}

void pre(abstract_heapt *heap) {
  if (empty(heap, list1))
    hashCode1=0;
  else
    hashCode1=1;
  if (empty(heap, list2))
    hashCode2=0;
  else
    hashCode2=1;

  iterator(heap, it1, list1);
  iterator(heap, it2, list2);
}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it1) || hasNext(heap, it2);
}

void body(abstract_heapt *heap) {
  if (hasNext(heap, it1))
  {
    obj1=next(heap, it1);
    hashCode1=31 * hashCode1 + obj1;
  }
  if (hasNext(heap, it2))
  {
    obj2=next(heap, it2);
    hashCode2=31 * hashCode2 + obj2;
  }
}

_Bool assertion(abstract_heapt *heap) {
  return !alias(heap, list1, list2) || hashCode1 == hashCode2;
}

_Bool inv_check(abstract_heapt *heap) {
  return is_path(heap, list1, it1) && is_path(heap, list2, it2) && (!alias(heap, list1, list2) || (alias(heap, it1, it2) && hashCode1 == hashCode2));
}

_Bool inv_assume(abstract_heapt *heap) {
  return is_path(heap, list1, it1) && is_path(heap, list2, it2) && (!alias(heap, list1, list2) || (alias(heap, it1, it2) && hashCode1 == hashCode2));
}
