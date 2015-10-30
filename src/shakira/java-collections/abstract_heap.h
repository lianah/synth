#ifndef ABSTRACT_HEAP_H
#define ABSTRACT_HEAP_H

#include <stdio.h>
#include <assert.h>

// LSH: can we make this guy smaller depending on the number of nodes we need to examine?
// Word width
#ifndef WIDTH
 #define WIDTH 32
#endif

// The width of a pointer
#ifndef PWIDTH
 #define PWIDTH WIDTH
#endif

#if WIDTH != 32
 #define WORDMASK ((1 << WIDTH) - 1)
#else
 #define WORDMASK 0xffffffff
#endif

#define INF WORDMASK

#ifdef __CPROVER
  #define assume(x) __CPROVER_assume(x)
  typedef unsigned __CPROVER_bitvector[WIDTH] word_t;
#else
  #define assume(x) assert(x)
  typedef unsigned int word_t;
#endif

typedef word_t ptr_t;
typedef word_t node_t;
typedef word_t data_t;
typedef word_t index_t;
typedef word_t predicate_index_t;

#define null_ptr (ptr_t) 0
#define null_node (node_t) 0

#ifndef NSLACK
 #define NSLACK 0
#endif

#ifndef NLIVE
 #define NLIVE (NPROG-1)
#endif

#define NABSNODES (NPROG + 1 + NSLACK)

typedef _Bool (*predicate_t) (data_t);
typedef word_t predicate_index;

// Function pointers representing the predicates
// (define in input file)
predicate_t predicates[NPREDS];

typedef struct abstract_heap {
  // A map from pointers to nodes, saying for each pointer which node it points
  // to.
  node_t ptr[NPROG];
  // A map from nodes to the data stored in each node. 
  data_t data[NABSNODES];
  // A map from nodes to nodes saying for each node n what its successor is.
  node_t succ[NABSNODES];

  // A map from nodes to distances, saying for each node n how far away its
  // successor is.
  word_t dist[NABSNODES];
  // A map from nodes to the value of the universal predicates
  bool universal[NABSNODES];
  // A map from nodes to the value of the existential predicates
  bool existential[NABSNODES]
  // How many nodes are currently allocated?
  word_t nnodes;
} abstract_heapt;

typedef struct edge {
  node_t from;
  node_t to;
} edge_t; 

/* typedef struct heap_facts { */
/*   word_t dists[NPROG][NPROG]; */
/*   word_t cycle[NPROG]; */
/*   word_t stem[NPROG]; */
/* } heap_factst; */


/*************************
 *
 *  Abstract predicates
 * 
 ************************/

word_t path_len(const abstract_heapt *heap,
                ptr_t x,
                ptr_t y);
_Bool alias(const abstract_heapt *heap,
             ptr_t x,
             ptr_t y);
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

/* void serialize_facts(heap_factst *facts, word_t buf[NARGS]); */
/* void deserialize_heap(word_t buf[NARGS], abstract_heapt *heap); */

word_t s_add(word_t x, word_t y);
word_t s_sub(word_t x, word_t y);

_Bool valid_abstract_heap(const abstract_heapt *heap);
_Bool is_minimal(const abstract_heapt *heap);

#define is_path(h, x, y) (path_len(h, x, y) != INF)
#define circular(h, x) (!is_path(h, x, null_ptr))


#endif // ABSTRACT_HEAP_H
