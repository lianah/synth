#include "abstract_heap.h"

extern void pre(abstract_heapt *heap);
extern void post(abstract_heapt *heap);
extern _Bool cond(const abstract_heapt *heap);
extern void body(abstract_heapt *pre);
extern _Bool assertion(const abstract_heapt *heap);
extern _Bool inv(const abstract_heapt *heap);
extern void init_predicates();
abstract_heapt nondet_heap(); 

void main(void) {
   abstract_heapt h; 

  /* assert(NABSNODES >= (NLIVE*2) + 1); */
  init_predicates();
  
  assume(valid_abstract_heap(&h));

  // Base.
  pre(&h);
  assert(inv(&h));

  h = nondet_heap();

  assume (valid_abstract_heap(&h));
  
  if (inv(&h)) {
    if (cond(&h)) {
      // Induction.
      body(&h);
      assert(inv(&h));
    }  else { 
       // Property. 
      assert(assertion(&h)); 
     } 
  }
}
