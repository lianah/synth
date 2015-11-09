#include "abstract_heap.h"

extern void pre(abstract_heapt *heap);
extern void post(abstract_heapt *heap);
extern _Bool cond(const abstract_heapt *heap);
extern void body(abstract_heapt *pre);
extern _Bool assertion(const abstract_heapt *heap);
extern _Bool inv_check(const abstract_heapt *heap);
extern _Bool inv_assume(const abstract_heapt *heap);

extern void init_predicates();
extern void init_heap(abstract_heapt *heap);

abstract_heapt nondet_heap(); 

void main(void) {
  abstract_heapt h; 
   
  init_predicates();
  init_heap(&h);
  assume(valid_abstract_heap(&h));

  // Base.
  pre(&h);
  assert(inv_check(&h));

  h = nondet_heap();
  init_heap(&h);
  assume (valid_abstract_heap(&h));

  /* assume(inv(&h)); */
  /* assume(cond(&h)); */
  /* assert(0); */

  if (inv_assume(&h)) {
    if (cond(&h)) {
      // Induction.
      body(&h);
      assert(inv_check(&h));
     }  else {
      // Property.
       assert(assertion(&h));
    }
  }
}
