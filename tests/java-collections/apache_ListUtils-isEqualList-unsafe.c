#include "abstract_heap.h"

// Run with -DNPROG=5

  /*public static boolean isEqualList(final Collection<?> list1, final Collection<?> list2) {
        if (list1 == list2) {
            return true;
        }
        if (list1 == null || list2 == null || list1.size() != list2.size()) {
            return false;
        }

        final Iterator<?> it1 = list1.iterator();
        final Iterator<?> it2 = list2.iterator();
        Object obj1 = null;
        Object obj2 = null;

	res = true;
        while (it1.hasNext() && it2.hasNext()) {
            obj1 = it1.next();
            obj2 = it2.next();

            if (!(obj1 == null ? obj2 == null : obj1.equals(obj2))) {
	        res = false
                //return false;
            }
        }

        return res && !(it1.hasNext() || it2.hasNext());
    }*/

ptr_t list1 = 1;
ptr_t list2 = 2;
ptr_t it1=3;
ptr_t it2=4;

data_t obj1;
data_t obj2;
_Bool result;
_Bool has_returned;

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
  has_returned = 0;

  if (!has_returned)
  {
    iterator(heap, it1, list1);
    iterator(heap, it2, list2);
  }

  if (alias(heap, list1, list2)) {has_returned=1; result=1;}
  if (!has_returned)
    if (is_null(heap, list1) || is_null(heap, list2) || size(heap, list1) != size(heap, list2))
    {
      has_returned=1;
      result=0;
    }

}

_Bool cond(abstract_heapt *heap) {
  return hasNext(heap, it1) && hasNext(heap, it2);
}

void body(abstract_heapt *heap) {
  obj1=next(heap, it1);
  obj2=next(heap, it2);

  if (obj1!=obj2) {
    result=0;
  }
}

_Bool assertion(abstract_heapt *heap) {
  if (result) {
    if(hasNext(heap, it1) || hasNext(heap, it2))
      result = 0;
    /* else */
    /*   result = 1; */
  }


  return  result == 0 || (empty(heap, list1) && empty(heap, list2)) ||
    (!empty(heap, list1) && !empty(heap, list2) &&
     max(heap, list1, null_ptr) != max(heap, list2, null_ptr));
}

_Bool inv_check(abstract_heapt *heap) {
  return result==0 ||
    (//size(heap, list1) == size(heap, list2) &&
     //path_len(heap, it1, null_ptr) == path_len(heap, it2, null_ptr) &&
     ((alias(heap, list1, it1) && alias(heap, list2, it2)) ||
      (!alias(heap, list1, it1) && !alias(heap, list2, it2) && 
       max(heap, list1, it1) == max(heap, list2, it2))));
}

_Bool inv_assume(abstract_heapt *heap) {
  return result==0 ||
    (//size(heap, list1) == size(heap, list2) &&
     //path_len(heap, it1, null_ptr) == path_len(heap, it2, null_ptr) &&
     ((alias(heap, list1, it1) && alias(heap, list2, it2)) ||
      (!alias(heap, list1, it1) && !alias(heap, list2, it2) && 
       max(heap, list1, it1) == max(heap, list2, it2))));

}
