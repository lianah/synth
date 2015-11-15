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

void debug_assert (_Bool x, char* tag);

#ifdef __CPROVER
  #define Assume(x) __CPROVER_assume(x)
  #define Assert(x, tag) __CPROVER_assert(x, tag)
  typedef unsigned __CPROVER_bitvector[WIDTH] word_t;
  typedef unsigned __CPROVER_bitvector[2] bool_t; 
#else
  #define Assume(x) assert(x)
  #define Assert(x, tag) debug_assert(x, tag)
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

/* typedef struct sorted_edge { */
/*   bool_t is_sorted; */
/*   data_t min; */
/*   data_t max; */
/* } sorted_edget; */

#define null_ptr (ptr_t) 0
#define null_node (node_t) 0
#define INVALID (word_t) INF
#define bool_unknown (bool_t) 2
#define bool_true (bool_t) 1
#define bool_false (bool_t) 0

typedef _Bool (*predicate_t) (data_t);

// Function pointers representing the predicates
// (define in input file)
predicate_t predicates[NPREDS];



typedef struct abstract_heap {
  // A map from pointers to nodes, saying for each pointer which node
  // it points to (INVALID if the pointer has been invalidated).
  
  node_t ptr[NPROG];

  // Indicates if the pointer is an iterator or not.
  // (initialized in input file)
  _Bool is_iterator[NPROG];


  // A map from nodes to nodes saying for each node n what its successor is.
  node_t succ[NABSNODES];

  // A map from nodes to nodes saying for each node n what its predecessor is.
  node_t prev[NABSNODES];

  // A map from nodes to the data stored in each node. 
  data_t data[NABSNODES];

  // A map from nodes to the number of nodes abstracted by the node's outgoing edge.
  word_t dist[NABSNODES];

  // A map from nodes to the value of the universal predicates
  bool_t universal[NABSNODES][NPREDS];

  // A map from nodes to the value of the existential predicates
  //bool_t existential[NABSNODES][NPREDS];

  // How many nodes are currently allocated?
  word_t nnodes;

  // A map from nodes to the value of the sorted predicate
  bool_t sorted[NABSNODES];

  // A map from nodes to the min value on the edge
  data_t min[NABSNODES];

  // A map from nodes to the max value on the edge 
  data_t max[NABSNODES];

} abstract_heapt;

node_t deref(const abstract_heapt *heap,
	     ptr_t p);



/*************************
 *
 *  Abstract "predicates"
 * 
 ************************/

word_t path_len(const abstract_heapt *heap,
                ptr_t x,
		ptr_t y);

_Bool is_path(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y);

_Bool alias(const abstract_heapt *heap,
	    ptr_t x,
	    ptr_t y);
_Bool is_null(const abstract_heapt *heap,
	      ptr_t x);	      


/* Check existential property (to be used in assert only) */
/* bool_t exists(const abstract_heapt *heap, */
/* 	      ptr_t x, */
/* 	      ptr_t y, */
/* 	      predicate_index_t pi); */
/* /\* Assume existential property *\/ */
/* _Bool exists_assume(const abstract_heapt *heap, */
/* 		     ptr_t x, */
/* 		     ptr_t y, */
/* 		     predicate_index_t pi); */

/* Check universal property (to be used in assert only)*/
bool_t forall(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y,
	      predicate_index_t pi);

/* Assume universal property */
_Bool forall_assume(const abstract_heapt *heap,
		    ptr_t x,
		    ptr_t y,
		    predicate_index_t pi);


bool_t sorted(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y);

data_t min(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y);

data_t max(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y);

/*************************
 *
 *  Abstract accessors
 * 
 ************************/

/* Positional get */
data_t getP(abstract_heapt *heap,
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

/* Assign to it the iterator of list */
void iterator(abstract_heapt* h,
	      ptr_t it,
	      ptr_t list);

void iteratorP(abstract_heapt* h,
	      ptr_t it,
	      ptr_t list,
        index_t i);


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

/* Iterator remove: removes the last node returned by next */
void removeI(abstract_heapt *heap,
	     ptr_t x);

/* Iterator next */
word_t next(abstract_heapt *heap,
	    ptr_t x);

/* Iterator has next */
_Bool hasNext(abstract_heapt *heap,
	      ptr_t x);

/* Return the next index pointed to by iterator */
index_t nextIndex(abstract_heapt *heap,
		  ptr_t x);

/* Iterator next */
word_t previous(abstract_heapt *heap,
		ptr_t x);

/* Iterator has next */
_Bool hasPrevious(abstract_heapt *heap,
		   ptr_t x);

/* Return the next index pointed to by iterator */
index_t previousIndex(abstract_heapt *heap,
		      ptr_t x);



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
  
  * Each node has in-degree 1 (except of null_node)

  * All reachable nodes are named

  * For each edge:
      * if univ == bool_true then exists = bool_true
      * if exists == bool_false then univ == bool_false
      * all edges of length 1 have exists and forall true
      * if length is 2 and exists == bool_true then univ = bool_true

  * For each node x != null:
      * succ(x) = x + 1 or succ(x) = null
      * exists[x] != bool_unknown and univ[x] != bool_unknown
      * if x is reachable then succ(x) != INVALID
      * if is_iterator(x) = 0 then prev(x) == null (lists cannot point to the middle of a list)
      
  * For each ptr p:
      * TODO: is_path(p, null)

  * For the null node:
      * univ[null] = bool_unknown
      * exist[null] = bool_unknown
      * succ(null) == null
      * prev(null) == null
      * dist(null) == 0
      * is_iterator[null] = 0
      
  * FIXME: check that predicates are consistent??
  * 
 */
_Bool valid_abstract_heap(const abstract_heapt *heap);
_Bool is_minimal(const abstract_heapt *heap);

#define empty(h, x) is_null(h, x)
#define size(h, x) path_len(h, x, null_ptr)

#ifdef __CPROVER
#define dump_heap(x, y, z) {}
#else

void dump_heap(abstract_heapt *heap,
	       const char* heap_name,
	       const char* pretty_args);
#endif


/* #define circular(h, x) (!is_path(h, x, null_ptr)) */


#endif // ABSTRACT_HEAP_H
