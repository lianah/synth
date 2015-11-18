/*
ListIterator<Integer> it = list.listIterator();
Integer min = it.next();

while(it.hasNext()) {
    //Inv: forall(list,i,min <=v) && exists(list,i, min == v)
    
    Integer current = it.next();
    if (current < min) {
	min = current;
    }
}

//assert(forall(list,n,min <= v) && exists(list,n,min == v));
*/

include "abstract_heap.h"

// Run with -DNPROG=3 and -DNPRED=2


ptr_t list = 1;
ptr_t iterator = 2;

word_t min; 
word_t current; 

_Bool eval_old_pred(data_t val, predicate_t foo) {
  aux = min;
  min = old_min;
  _Bool res = foo(val);
  min = aux;
}

_Bool smaller(data_t val) {
  return val <= min;
}

_Bool equal(data_t val) {
  return val == min;
}

void init_predicates() {
  predicates[0] = smaller();
  predicates[1] = equal();
}

void pre(abstract_heapt *heap) {
  // LSH FIXME: make special transformer?
  //ListIterator<Int> iterator = list.listIterator()
  assign(heap, iterator, list);
  min = next(heap, iterator);
}

_Bool cond(abstract_heapt *heap) {
  return has_next(heap, iterator);
}

void body(abstract_heapt *heap) {
  old_min = min;
  data_t val = nondet_data_t(); // forall val. 
  _Bool pre0 = smaller(val, min); // val <= min
  _Bool pre1 = equal(val, min); // val == min
  
  current = next(heap, iterator);
  if (current < min) {
    min = current; 
  }
  min = 0;

  _Bool post0 = smaller(val, min); // val <= min'
  _Bool post1 = equal(val, min); // val == min'
  // forall val. val <= min => val <= min'
  Assert (!pre0 || post0);
  Assert (!pre1 || post1);
}

_Bool assertion(abstract_heapt *heap) {
  return forall(heap, list, null_ptr, 0) &&
         exists(heap, list,  null_ptr, 1);
}

_Bool inv_assume(abstract_heapt *heap) {
  return is_path(heap, list, iterator) &&
         forall_assume(heap, list, iterator, 0);

_Bool inv_check(abstract_heapt *heap) {
  return is_path(heap, list, iterator) &&
         forall(heap, list, iterator, 0);
}
