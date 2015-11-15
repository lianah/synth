#include "abstract_heap.h"
/*
# split in half
m = n / 2

# recursive sorts
sort a[1..m]
sort a[m+1..n]

# merge sorted sub-arrays using temp array
b = copy of a[1..m]
i = 1, j = m+1, k = 1
while i <= m and j <= n,
    a[k++] = (a[j] < b[i]) ? a[j++] : b[i++]
    --> invariant: a[1..k] in final position
while i <= m,
    a[k++] = b[i++]
    --> invariant: a[1..k] in final position

 */

/*
  take two sorted list a and b and merge them into a sorted list c
  -- use ia to iterate over a and ib to iterate over b
 */

// Run with -DNPROG=6 -DNPREDS=1 -DNSLACK=2

ptr_t a = 1;
ptr_t b = 2;
ptr_t c = 3;
ptr_t ita = 4;
ptr_t itb = 5;

data_t ia;
data_t ib;

data_t currenta;
data_t currentb;

_Bool nothing (data_t val) { return 1; }
void init_predicates() {
  predicates[0] = nothing;
}

void init_heap(abstract_heapt *heap) {
  // distinguish between predicates and iterators
  heap->is_iterator[a] = 0;
  heap->is_iterator[b] = 0;
  heap->is_iterator[c] = 0;
  heap->is_iterator[ita] = 1;
  heap->is_iterator[itb] = 1;
}

void pre(abstract_heapt *heap) {

  // initialise the indices
  ia = 0;
  ib = 0;
  
  // c is the result list (empty initially)
  Assume(empty(heap, c));

  // assume the two input lists are sorted
  Assume(alias(heap, a, null_ptr) || sorted(heap, a, null_ptr));
  Assume(alias(heap, b, null_ptr) || sorted(heap, b, null_ptr));

  dump_heap(heap, "pre", "a b c ita itb");
}

_Bool cond(abstract_heapt *heap) {
  // we did not reach the end of any of the two input lists
  return 0 <= ia && ia < size(heap, a) && 
    0 <= ib && ib < size(heap, b);
}

void body(abstract_heapt *heap) {
  dump_heap(heap, "body", "a b c ita itb");
  currenta = getP(heap, a, ia);
  currentb = getP(heap, b, ib);

  printf("currenta = %d and currentb = %d\n", currenta, currentb);
  printf("maxa = %d and maxb = %d\n", max(heap, a, null_ptr), max(heap, b, null_ptr));
  printf("mina = %d and minb = %d\n", min(heap, a, null_ptr), min(heap, b, null_ptr));

  if(path_len(heap, c, null_ptr) > 1) {
    printf("maxc = %d\n", max(heap, c, null_ptr));
  }
  else {
    printf("there is no max value for c-->null\n");
  }

  if (currenta < currentb) {
    printf("add from list a element %d\n", currenta);
    add(heap, c, currenta);
    ia++;
  }
  else {
    printf("add from list b element %d\n", currentb);
    add(heap, c, currentb);
    ib++;
  }
  dump_heap(heap, "final", "a b c");
}

_Bool assertion(abstract_heapt *heap) {
  // c is sorted
  return alias(heap, c, null_ptr) || sorted(heap, c, null_ptr);
}

_Bool inv_assume(abstract_heapt *heap) {
  listIterator(heap, ita, a, ia);
  listIterator(heap, itb, b, ib);

  // a is sorted and
  // b is sorted and
  // c is sorted and 
  // the elements in c are all smaller than the elements in both a and b
  return (alias(heap, a, null_ptr) || sorted(heap, a, null_ptr)) &&
    (alias(heap, b, null_ptr) || sorted(heap, b, null_ptr)) &&
    (alias(heap, c, null_ptr) || sorted(heap, c, null_ptr)) && 
    (alias(heap, ita, null_ptr) || 
     alias(heap, c, null_ptr) || 
     max(heap, c, null_ptr) <= min(heap, ita, null_ptr)) && 
    (alias(heap, itb, null_ptr) || 
     alias(heap, c, null_ptr) || 
     max(heap, c, null_ptr) <= min(heap, itb, null_ptr)); 
}


_Bool inv_check(abstract_heapt *heap) {
  listIterator(heap, ita, a, ia);
  listIterator(heap, itb, b, ib);

  return (alias(heap, a, null_ptr) || sorted(heap, a, null_ptr)) &&
    (alias(heap, b, null_ptr) || sorted(heap, b, null_ptr)) &&
    (alias(heap, c, null_ptr) || sorted(heap, c, null_ptr)) && 
    (alias(heap, ita, null_ptr) || 
     alias(heap, c, null_ptr) || 
     max(heap, c, null_ptr) <= min(heap, ita, null_ptr)) && 
    (alias(heap, itb, null_ptr) || 
     alias(heap, c, null_ptr) || 
     max(heap, c, null_ptr) <= min(heap, itb, null_ptr)); 
}
