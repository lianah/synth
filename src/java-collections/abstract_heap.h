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
  typedef unsigned __CPROVER_bitvector[2] bool_t; 
#else
  #define assume(x) assert(x)
  typedef unsigned int word_t;
  typedef int bool_t; 
#endif

#ifndef NSLACK
 #define NSLACK 0
#endif

#ifndef NLIVE
 #define NLIVE (NPROG-1)
#endif

#ifndef NPREDS
 #define NPREDS 1
#endif

#define NABSNODES (NPROG + 1 + NSLACK)


typedef word_t ptr_t;
typedef word_t node_t;
typedef word_t data_t;
typedef word_t index_t;
typedef word_t predicate_index_t;

#define null_ptr (ptr_t) 0
#define null_node (node_t) 0
//#define undef (word_t) INF
#define bool_unknown (bool_t) 2
#define bool_true (bool_t) 1
#define bool_false (bool_t) 0

typedef _Bool (*predicate_t) (data_t);

// Function pointers representing the predicates
// (define in input file)
predicate_t predicates[NPREDS];

typedef struct abstract_heap {
  // A map from pointers to nodes, saying for each pointer which node it points
  // to.
  node_t ptr[NPROG];

  // A map from nodes to the data stored in each node. 
  // data_t data[NABSNODES];
  // A map from nodes to nodes saying for each node n what its successor is.
  node_t succ[NABSNODES];

  // A map from nodes to the data stored in each node. 
  // data_t data[NABSNODES];
  // A map from nodes to nodes saying for each node n what its successor is.
  data_t data[NABSNODES];

  // A map from nodes to distances, saying for each node n how far away its
  // successor is.
  word_t dist[NABSNODES];

  // A map from nodes to the value of the universal predicates
  bool_t universal[NABSNODES][NPREDS];

  // A map from nodes to the value of the existential predicates
  bool_t existential[NABSNODES][NPREDS];

  // How many nodes are currently allocated?
  word_t nnodes;
} abstract_heapt;

typedef struct edge {
  node_t from;
  node_t to;
} edge_t; 


/*************************
 *
 *  Abstract "predicates"
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

// return bool_t since there is loss of precision
bool_t exists(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y,
	      predicate_index_t pi);

bool_t forall(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y,
	      predicate_index_t pi);

bool_t sorted(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y);


/*************************
 *
 *  Abstract accessors
 * 
 ************************/

/* Positional get */
data_t getP(const abstract_heapt *heap,
	    ptr_t x,
	    index_t i);

/* Iterator get (does not exist!) */
data_t getI(const abstract_heapt *heap,
	    ptr_t x);

		 
/*************************
 *
 *  Abstract transformers
 * 
 ************************/

/* Creates a new list */
void abstract_new(abstract_heapt *heap,
                  ptr_t x);

/* Adds element at end of list */
void add(abstract_heapt *heap,
	 ptr_t x,
	 data_t val);

void assign(abstract_heapt *heap,
	    ptr_t x,
	    ptr_t y);

/* Removes all elements from list */
void clear(abstract_heapt *heap,
	   ptr_t x);

/*************************
 *  Positional operators
 ************************/


/* Positional set */
void setP(abstract_heapt *heap,
	  ptr_t x,
	  index_t i,
	  data_t val);


/* Positional add */
void addP(abstract_heapt *heap,
	  ptr_t x,
	  index_t i,
	  data_t val);

/* Positional remove */
void removeP(abstract_heapt *heap,
	    ptr_t x,
	    index_t i);

/*************************
 *  Iterator operators
 ************************/


/* Iterator add */
void addI(abstract_heapt *heap,
	 ptr_t x,
	 data_t val);

// LSH FIXME: this is not the actual Java semantics (in Java it sets the
// last value returned!), same for remove
/* Iterator set */
void setI(abstract_heapt *heap,
	  ptr_t x,
	  data_t val);

/* Iterator remove */
void removeI(abstract_heapt *heap,
	     ptr_t x);

/* Iterator next */
word_t next(abstract_heapt *heap,
	    ptr_t x);

/* Iterator has next */
_Bool has_next(abstract_heapt *heap,
	       ptr_t x);

/* Return the next index pointed to by iterator */
index_t nextIndex(abstract_heapt *heap,
		  ptr_t x);

// TODO: PREVIOUS not yet supported

/* void serialize_facts(heap_factst *facts, word_t buf[NARGS]); */
/* void deserialize_heap(word_t buf[NARGS], abstract_heapt *heap); */

word_t s_add(word_t x, word_t y);
word_t s_sub(word_t x, word_t y);

bool_t and(bool_t x, bool_t y);
bool_t or(bool_t x, bool_t y);

/* _Bool and_preds(predicate_t x, predicate_t y); */
/* _Bool or_preds(bool_t x, bool_t y); */


/*
  A valid abstract heap has the following properties:
  * each node has in-degree 1
  * all reachable nodes are named
  * predicates for all reachable nodes are known
  * if forall is true on an edge so is exists
  * if exists is false then so is forall
  * if length is 1 and existential is true so is universal
  * check that predicates are consistent??
  * for each node x != null, succ(x) = x + 1 or succ(x) = null
  * for the null node data[null] = undef, univ[null] = bool_unknown, exist[null] = bool_unknown
  * TODO: more stuff? 
  * 
 */
_Bool valid_abstract_heap(const abstract_heapt *heap);
_Bool is_minimal(const abstract_heapt *heap);

#define is_path(h, x, y) (path_len(h, x, y) != INF)
#define empty(h, x) is_null(h, x)
#define iterator(h, it, list) assign(h, it, list)
#define has_next(h, it) !is_null(h, it)

/* #define circular(h, x) (!is_path(h, x, null_ptr)) */


#endif // ABSTRACT_HEAP_H