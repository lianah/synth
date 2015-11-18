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

extern void init_counterexample(abstract_heapt *heap);
extern void inductive_counterexample(abstract_heapt *heap);

abstract_heapt nondet_heap(); 

void main(void) {
   abstract_heapt h; 

  init_predicates();
  
  /* init_counterexample(&h); */
  /* init_heap(&h); */

  /* Assert (valid_abstract_heap(&h), "INV_FAIL: Base case."); */

  /* // Base. */
  /* pre(&h); */
  /* Assert(inv_check(&h), "INV_FAIL: Assumption"); */

  inductive_counterexample(&h);
  init_heap(&h);
  Assert (valid_abstract_heap(&h), "INV_FAIL: Assumption");
  
  if (inv_assume(&h)) {
    if (cond(&h)) {
      // Induction.
      body(&h);
      Assert(inv_check(&h), "INV_FAIL: Inductive step.");
    }  else { 
       // Property.
      Assert(assertion(&h), "INV_FAIL: Property entailment."); 
     } 
  }
}
