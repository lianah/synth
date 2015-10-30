#include "abstract_heap.h"

#include <string.h>


#ifndef __CPROVER
abstract_heapt nondet_heap() {
  abstract_heapt h;
  return h;
}
#endif


/*
 * Dereference p -- which node does p point to?
 */
static node_t deref(const abstract_heapt *heap,
                    ptr_t p) {
  // Ensure p is a real pointer.
  assume(p < NPROG);
  return heap->ptr[p];
}

/*
 * Next operator -- which node is in n's next pointer?
 */
static node_t next(const abstract_heapt *heap,
                   node_t n) {
  // Ensure n is an allocated node.
  assume(n < NABSNODES);
  return heap->succ[n];
}

/*
 * How far away is n's successor?
 */
static word_t dist(const abstract_heapt *heap,
                   node_t n) {
  assume(n < NABSNODES);
  return heap->dist[n];
}


/*
 * x = n;
 *
 * x is a pointer, n is a graph node.
 */
/* static void destructive_assign_ptr(abstract_heapt *heap, */
/*                                    ptr_t x, */
/*                                    node_t n) { */
/*   assume(x < NPROG); */
/*   assume(n < NABSNODES); */
/*   heap->ptr[x] = n; */
/* } */

/* /\* */
/*  * x.n = y; */
/*  * */
/*  * x and y are nodes. */
/*  *\/ */
/* static void destructive_assign_next(abstract_heapt *heap, */
/*                                     node_t x, */
/*                                     node_t y, */
/*                                     word_t dist) { */
/*   assume(x < NABSNODES); */
/*   assume(y < NABSNODES); */
/*   heap->succ[x] = y; */
/*   heap->dist[x] = dist; */
/* } */

/* /\* */
/*  * x = y; */
/*  * */
/*  * x and y are pointers. */
/*  *\/ */
/* void abstract_assign(abstract_heapt *heap, */
/*                      ptr_t x, */
/*                      ptr_t y) { */
/*   assume(x < NPROG); */
/*   assume(y < NPROG); */

/*   //copy_abstract(pre, post); */

/*   node_t py = deref(heap, y); */
/*   destructive_assign_ptr(heap, x, py); */
/* } */

/* /\* */
/*  * Allocate a new node. */
/*  *\/ */
/* static node_t destructive_alloc(abstract_heapt *heap) { */
/*   node_t n; */

/*   // assert(heap->nnodes < NABSNODES); */
/*   assume(heap->nnodes < NABSNODES); */
/*   return heap->nnodes++; */
/* } */

/* /\* */
/*  * x = new(); */
/*  *\/ */
/* void abstract_new(abstract_heapt *heap, */
/*                   ptr_t x) { */
/*   assume(x < NPROG); */

/*   //copy_abstract(pre, post); */

/*   // Just allocate a new node and have x point to it. */
/*   node_t n = destructive_alloc(heap); */
/*   destructive_assign_next(heap, n, null_node, 1); */
/*   destructive_assign_ptr(heap, x, n); */
/* } */


/*************************
 *
 *  Abstract predicates
 * 
 ************************/

word_t path_len(const abstract_heapt *heap,
                ptr_t x,
                ptr_t y) {
  word_t curr_dist = 0;
  node_t n = deref(heap, x);
  node_t yn = deref(heap, y);
  word_t i;

  for (i = 0; i < NABSNODES+1; i++) {
    if (n == yn) {
      return curr_dist;
    }

    curr_dist = s_add(curr_dist, dist(heap, n));
    n = next(heap, n);
  }

  return INF;


}
_Bool alias(const abstract_heapt *heap,
             ptr_t x,
	    ptr_t y) {
  word_t alias(const abstract_heapt *heap,
             ptr_t x,
             ptr_t y) {
  node_t xn = deref(heap, x);
  node_t yn = deref(heap, y);

  return xn == yn;
}

}
_Bool is_null(const abstract_heapt *heap,
	      ptr_t x);	      

_Bool exists(const abstract_heapt *heap,
	     ptr_t x,
	     ptr_t y,
	     predicate_index i);

_Bool forall(const abstract_heapt *heap,
	     ptr_t x,
	     ptr_t y,
	     predicate_index i);

_Bool sorted(const abstract_heapt *heap,
	     ptr_t x,
	     ptr_t y);


/*************************
 *
 *  Abstract accessors
 * 
 ************************/

data_t get(const abstract_heapt *heap,
	   ptr_t x,
	   index_t i);

index_t index_of(const abstract_heapt *heap,
		 data_t value);

		 
/*************************
 *
 *  Abstract transformers
 * 
 ************************/

void set(const abstract_heapt *heap,
	 ptr_t x,
	 index_t i,
	 data_t val);

void add(const abstract_heapt *heap,
	 ptr_t x,
	 index_t i,
	 data_t val);

void remove(const abstract_heapt *heap,
	    ptr_t x,
	    index_t i);

void abstract_assign(abstract_heapt *heap,
                     ptr_t x,
                     ptr_t y);

void increment(abstract_heapt *heap,
	       ptr_t x);
