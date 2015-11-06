#include "abstract_heap.h"

#include <string.h>


#ifndef __CPROVER
abstract_heapt nondet_heap() {
  abstract_heapt h;
  return h;
}

data_t nondet_data_t() {
  data_t d;
  return d;
}
#else

data_t nondet_data_t();

#endif


/*
 * Dereference p -- which node does p point to?
 */
static node_t deref(const abstract_heapt *heap,
                    ptr_t p) {
  // Ensure p is a real pointer.
  assume(p < NPROG);
  assert (heap->ptr[p] != INVALID);
  return heap->ptr[p];
}

/*
 * Check if p is an iterator. 
 */
static _Bool is_iterator(const abstract_heapt *heap,
			 ptr_t p) {
  // Ensure p is a real pointer.
  assume(p < NPROG);
  return heap->is_iterator[p];
}


/*
 * Succ operator -- which node is in n's succ pointer?
 */
static node_t succ(const abstract_heapt *heap,
                   node_t n) {
  // Ensure n is an allocated node.
  assume(n < NABSNODES);
  return heap->succ[n];
}

/*
 * Prev operator -- which node is in n's predecessor pointer?
 */
static node_t prev(const abstract_heapt *heap,
                   node_t n) {
  // Ensure n is an allocated node.
  assume(n < NABSNODES);
  assert(n != null_node);
  return heap->prev[n];
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
 * How far away is n's successor?
 */
static word_t data(const abstract_heapt *heap,
                   node_t n) {
  assume(n < NABSNODES);
  assert(n != null_node);
  return heap->data[n];
}


/*
 * What is the value of the i_th existential predicate for n ?
 */
static bool_t get_exists(const abstract_heapt *heap,
			 node_t n,
			 predicate_index_t pi) {
  assume(n < NABSNODES);
  assume(pi < NPREDS);
  return heap->existential[n][pi];
}

/*
 * What is the value of the i_th universal predicate for n ?
 */
static bool_t get_univ(const abstract_heapt *heap,
		       node_t n,
		       predicate_index_t pi) {
  assume(n < NABSNODES);
  assume(pi < NPREDS);
  return heap->universal[n][pi];
}

/*
 * What is the value of the i_th universal predicate for n ?
 */
static _Bool eval_pred(predicate_index_t pi, data_t val) {
  assume(pi < NPREDS);
  return predicates[pi](val);
}

/*
 * x = n;
 *
 * x is a pointer, n is a graph node.
 */
static void assign_ptr(abstract_heapt *heap,
		       ptr_t x,
		       node_t n) {
  assume(x < NPROG);
  assume(n < NABSNODES);
  heap->ptr[x] = n;
}

static void assign_univ(abstract_heapt *heap,
			node_t nx,
			predicate_index_t pi,
			bool_t pred_val) {
  assume(nx < NABSNODES);
  assume(pi < NPREDS);
  heap->universal[nx][pi] = pred_val;
}

static void assign_exists(abstract_heapt *heap,
			  node_t nx,
			  predicate_index_t pi,
			  bool_t pred_val) {
  assume(nx < NABSNODES);
  assume(pi < NPREDS);
  heap->existential[nx][pi] = pred_val;
}


static void assign_succ(abstract_heapt *heap,
			node_t x,
			node_t y,
			word_t dist) {
  assume(x < NABSNODES);
  assume(y < NABSNODES);
  assert (dist);
  
  heap->succ[x] = y;
  heap->prev[y] = x;
  
  heap->dist[x] = dist;
  
  predicate_index_t pi = 0;
  if (dist == 1) {
    for (pi = 0; pi < NPREDS; ++pi) {
      // everything is true about elments in the empty set
      assign_univ(heap, x, pi, bool_true);
      // nothing exists in the empty set
      assign_exists(heap, x, pi, bool_false);
    }
  }
}

static void assign_data(abstract_heapt *heap,
			node_t x,
			data_t val) {
  assume(x < NABSNODES);
  assert (x != null_node);
  heap->data[x] = val;
}

/*
 * Allocate a new node.
 */
static node_t alloc(abstract_heapt *heap) {
  node_t n;
  assume(heap->nnodes < NABSNODES);
  return heap->nnodes++;
}


/*
 * Mark node as invalid (for remove and invalidating iterators).
 */
static void invalidate(abstract_heapt *heap,
		       node_t nx) {
  assert (nx != null_node);
  assert (nx < heap->nnodes);
  word_t i;
  for (i = 0; i < NPROG; ++i) {
    if (is_iterator(heap, i) &&
	heap->ptr[i] == nx) {
      heap->ptr[i] = INVALID;
    }
  }
}


/*
 * Mark node as invalid (for remove and invalidating iterators).
 */
static void invalidate_and_update(abstract_heapt *heap,
				  node_t nx,
				  node_t nnew) {
  assert (nx != null_node);
  assert (nx < heap->nnodes);
  word_t i;
  for (i = 0; i < NPROG; ++i) {
    if (heap->ptr[i] == nx) {
      if (heap->is_iterator[i]) {
	// invalidate pointers
	heap->ptr[i] = INVALID;
      } else {
	// lists now point to the new node
	heap->ptr[i] = nnew;
      }
    }
  }
}


/*
 * Clar the node (LSH FIXME: not sure we actually need to do this)
 */
static void clear_node(abstract_heapt* heap,
		       node_t nx) {
  assert (nx != null_node);
  assert (nx < heap->nnodes);
  word_t data;
  assign_data(heap, nx, data);
  assign_succ(heap, nx, null_node, 1);
}

/*
 * x = new();
 */
void abstract_new(abstract_heapt *heap,
                  ptr_t x) {
  assume(x < NPROG);

  // Just allocate a new node and have x point to it.
  node_t nx = alloc(heap);
  assign_succ(heap, nx, null_node, 1);
  assign_ptr(heap, x, nx);
}


/*
  Creates a new node nnew at distance 1 from nx and
  updates the predicates, succ and len for nx, and nnew  
*/
node_t subdivide(abstract_heapt *heap,
		 node_t nx) {
  assert (nx < NABSNODES);
  node_t succ_nx = succ(heap, nx);
  word_t nx_dist = dist(heap, nx);

  // Two cases: 
  //
  // (1): x has a direct successor, i.e. x -1> succ_nx
  // (2): x's successor is some distance > 1 away, i.e. x -k-> succ_nx
  if (nx_dist == 1) {
    // Case 1:
    //
    // x's successor is one step away, so return that
    return succ_nx;
  } else {
    // Case 2:
    //
    // x's successor is more than one step away, so we need to introduce
    // an intermediate node n, which will become x's successor 
    //
    // Pre state:
    //
    // x -k> succ_nx
    //
    // Heap state:
    //
    // nx -1-> nnew -(k-1)-> succ_nx
    //
    // Begin by allocating a new node between nx and succ_nx.
    node_t nnew = alloc(heap);
    word_t new_dist = s_sub(nx_dist, 1);
    predicate_index_t pi;
    for (pi = 0; pi < NPREDS; ++pi) {
      bool_t new_univ = get_univ(heap, nx, pi);
      bool_t new_exists = get_exists(heap, nx, pi);
      // Assume the predicates for the values stored at nnew
      // Only true universals are still true on the data
      if (new_univ == bool_true) {
	assume(eval_pred(pi, data(heap, nnew)));
	assign_univ(heap, nnew, pi, bool_true);
      } else {
	assign_univ(heap, nnew, pi, bool_unknown);
      }

      // Only false existentials are still false on the data
      if (get_exists == bool_false) {
	assume(!eval_pred(pi, data(heap, nnew)));
	assign_exists(heap, nnew, pi, bool_false);
      } else {
	assign_exists(heap, nnew, pi, bool_unknown);
      }
    }

    // Reassign nnew's succ pointer to nx's successor succ_nx
    assign_succ(heap, nnew, succ_nx, new_dist);
    // Reassign nx's succ pointer to the newly allocated node.
    assign_succ(heap, nx, nnew, 1);
    return nnew;
  }
}

/*
  Invalidate all the pointers from nx to null (excluding)
*/
extern void invalidate_succ(abstract_heapt* heap,
			    node_t nx) {
  assert (nx != null_node);

  node_t initial_nx = nx;
  
  nx = succ(heap, nx);

  word_t i;

  for (i = 1; i < NABSNODES; ++i) {
    if (nx == null_node)
      return;
    invalidate(heap, nx);
    nx = succ(heap, nx);
  }
}

/*
  Invalidate all the pointers from beginning of list to nx (excluding)
*/
extern void invalidate_prev(abstract_heapt* heap,
			    node_t nx) {
  assert (nx != null_node);

  node_t initial_nx = nx;
  
  nx = prev(heap, nx);

  word_t i;
  for (i = 1; i < NABSNODES; ++i) {
    // we want to exclude the first pointer
    if (prev(heap, nx) == null_node) {
      return;
    }
    invalidate(heap, nx);
    nx = prev(heap, nx);
  }
}


/*
 * Compute the value of forall pi on path (nx, ny)
 */
static bool_t path_forall(const abstract_heapt *heap,
			  node_t nx,
			  node_t ny,
			  predicate_index_t pi) {
  assert (0);
  return bool_unknown;
}

/*
 * Compute the value of exists pi on path (nx, ny)
 */
static bool_t path_exists(const abstract_heapt *heap,
			  node_t nx,
			  node_t ny,
			  predicate_index_t pi) {
  assert (0);
  return bool_unknown;
}


/*
 * Check that the heap is well formed.
 */
_Bool valid_abstract_heap(const abstract_heapt *heap) {
  // NULL points to the null node.
  if (heap->ptr[null_ptr] != null_node) {
    return 0;
  }

  /* if (is_iterator(heap, null_ptr) == 0) {  */
  /*   return 0;  */
  /* }  */

  // The null node doesn't point anywhere and
  // by convention has no predecessor.
  if (heap->succ[null_node] != null_node/* ||
					   heap->prev[null_node] != null_node*/) {
    return 0;
  }

  if (dist(heap, null_node) != 0) {
    return 0;
  }

  predicate_index_t pi;
  // null predicates are all unknown
  for (pi = 0; pi < NPREDS; ++pi) {
    if (get_exists(heap, null_node, pi) != bool_unknown) {
      return 0;
    }
    
    if (get_univ(heap, null_node, pi) != bool_unknown) {
      return 0;
    }
  }

  return is_minimal(heap);
}

_Bool is_minimal(const abstract_heapt *heap) {
  word_t is_named[NABSNODES];
  memset(is_named, 0, sizeof(is_named));

 word_t has_in_edge[NABSNODES];
 memset(has_in_edge, 0, sizeof(is_named));

  
  word_t nreachable = 0;

  ptr_t p;
  node_t n, m;
  word_t i;
  predicate_index_t pi; 

  // the null node is named
  //is_named[0] = 1;
  
  for (p = 0; p < NPROG; p++) {
    n = heap->ptr[p];
    is_named[n] = 1;

    // only allocated nodes
    if (n >= heap->nnodes) {
      return 0;
    }

    // check that named nodes have succ n + 1
    if (succ(heap, n) != null_node) {
      if (n + 1 != succ(heap, n)) 
	return 0;
      // make sure predecessors match
      if(prev(heap, succ(heap, n))!= n)
	return 0;

      // only iterators can have incoming edges
      has_in_edge[succ(heap, n)] = 1;
    }

    for (pi = 0; pi < NPREDS; ++pi) {
      bool_t e = get_exists(heap, n, pi);
      bool_t u = get_univ(heap, n, pi);

      // edges of length 1 have the predicates true
      if (dist(heap, n) == 1 &&
	  (e != bool_false || u != bool_true))
	return 0;
      
      if (e > bool_unknown || u > bool_unknown)
	return 0;
      
      // predicates are known for all nodes 
      if (n != null_node &&
	  (e == bool_unknown ||
	   u == bool_unknown)) {
	return 0;
      }
      // if the universal holds so does the existential
      if (u == bool_true && e == bool_false)
	return 0;
    }
  }

  // check that all nodes are named
  for (i = 0; i < NABSNODES-1; i++) {
    nreachable += is_named[i];
    if (is_named[i] && !is_named[succ(heap, i)]) {
      return 0;
    }
    if (i != null_node && dist(heap, i) <= 0) {
      return 0;
    }
  }

  for (i = 1; i < NPROG; ++i) {
    n = heap->ptr[i];
    // lists cannot have incoming edges
    if (heap->is_iterator[i] == 0 &&
	has_in_edge[n])
      return 0;
    // all nodes without incoming edges have prev(x) == null
    if (has_in_edge[i] == 1 &&
    	heap->prev[i] != null_node)
      return 0;
  }
  
  // If we're a fully reduced graph, we don't have any unreachable nodes.
  if (heap->nnodes != nreachable) {
    return 0;
  }

  //LSH size
  //if (nreachable > NLIVE*2 + 1) {
  if (nreachable > NLIVE + 2) {
    return 0;
  }
  
  for (i = 0; i < NABSNODES-1; i++) {
    if (i < heap->nnodes && !is_named[i])
      return 0;
  }

  // Check there are no unnamed, reachable nodes with indegree <= 1.
  // LSH: this says that the anonymous edges were smoothen
  /* for (n = 0; n < NABSNODES; n++) { */
  /*   if (!is_named[n] && is_reachable[n] && indegree[n] <= 1) { */
  /*     return 0; */
  /*   } */
  /* } */
  // LSH: what if we have x= new(); x = y (i.e. memory leak)
  
  return 1;
}

/*************************
 *
 *  Abstract "predicates"
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
    if (n == null_node) {
      return INF;
    }

    curr_dist = s_add(curr_dist, dist(heap, n));
    n = succ(heap, n);
  }
  
  assert (0);
  return INF;
}

_Bool is_path(const abstract_heapt *heap,
	       ptr_t x,
	       ptr_t y) {
  word_t curr_dist = 0;
  node_t n = deref(heap, x);
  node_t yn = deref(heap, y);
  word_t i;

  for (i = 0; i < NABSNODES+1; i++) {
    if (n == yn) {
      return 1;
    }
    if (n == null_node)
      return 0;

    n = succ(heap, n);
  }
  assert (0);
  return 0;
}


_Bool alias(const abstract_heapt *heap,
	    ptr_t x,
	    ptr_t y) {
  node_t xn = deref(heap, x);
  node_t yn = deref(heap, y);

  return xn == yn;
}

_Bool is_null(const abstract_heapt *heap,
	      ptr_t x) {
  return deref(heap, x) == null_node;
}

bool_t exists(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y,
	      predicate_index_t pi) {
  assume(is_path(heap, x, y));
  
  node_t nx = deref(heap, x);
  node_t ny = deref(heap, y);

  // This is technically the empty list so everything holds
  if (nx == ny) {
    return bool_false;
  }

  bool_t res = bool_false;
  word_t i;
  for (i = 0; i < NABSNODES; ++i) {
    if (nx == ny) {
      return res;
    }
    res = or (res, (bool_t)eval_pred(pi, data(heap, nx)));
    res = or(res, get_exists(heap, nx, pi));
    nx = succ(heap, nx);
  }
  // LSH FIXME: paper actually checks entailment
  return bool_unknown;
}


bool_t forall(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y,
	      predicate_index_t pi) {
  // LSH think about it!
  assume(is_path(heap, x, y));
  
  node_t nx = deref(heap, x);
  node_t ny = deref(heap, y);

  // This is technically the empty list so everything holds
  if (nx == ny) {
    return bool_true;
  }
  
  bool_t res = bool_true;
  word_t i;
  for (i = 0; i < NABSNODES; ++i) {
    if (nx == ny) {
      return res;
    }
    res = and(res, (bool_t)eval_pred(pi, data(heap, nx)));
    res = and(res, get_univ(heap, nx, pi));
    nx = succ(heap, nx);
  }
  // LSH FIXME: the paper actually cehcks that the predicates entail the current predicate
  return bool_unknown;
}

bool_t sorted(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y) {
  assert(0);
  return 0;
}


/*************************
 *
 *  Abstract accessors
 * 
 ************************/

/* Positional get */
data_t getP(const abstract_heapt *heap,
	    ptr_t list,
	    index_t i) {
  assert (!is_iterator(heap, list));
  assert(0);
  return 0;
}

/* Iterator get */
data_t getI(const abstract_heapt *heap,
	    ptr_t it) {
  assert (is_iterator(heap, it));
  node_t nit = deref(heap, it);
  assert (nit != null_node);
  return data(heap, nit);
}

		 
/*************************
 *
 *  Abstract transformers
 * 
 ************************/

/* Adds element at end of list */
void add(abstract_heapt *heap,
	 ptr_t list,
	 data_t val) {
  
  assert (!is_iterator(heap, list));
  node_t nlist = deref(heap, list);
  
  if ( nlist == null_node) {
    abstract_new(heap, list);
    nlist = deref(heap, list);
    assign_data(heap, nlist, val);
    return;
  }

  invalidate_succ(heap, nlist);
  
  word_t i;
  for (i = 0; i < NABSNODES; ++i) {
    if (succ(heap, nlist) == null_node) {
      node_t nnew = alloc(heap);
      assign_succ(heap, nnew, null_node, dist(heap, nlist));      
      assign_succ(heap, nlist, nnew, 1);
    }
    nlist = succ(heap, nlist);
  }
  return;
}

void assign(abstract_heapt *heap,
	    ptr_t x,
	    ptr_t y) {
  assume(x < NPROG);
  assume(y < NPROG);

  assert (is_iterator(heap, x) == is_iterator(heap, y));

  node_t py = deref(heap, y);
  assign_ptr(heap, x, py);
}

/* Removes all elements from list */
void clear(abstract_heapt *heap,
	   ptr_t x) {
  assert(0);
}

/*************************
 *  Positional operators
 ************************/


/* Positional set */
void setP(abstract_heapt *heap,
	  ptr_t list,
	  index_t i,
	  data_t val) {
  assert(!is_iterator(heap, list));
  assert(0);
}


/* Positional add */
void addP(abstract_heapt *heap,
	  ptr_t list,
	  index_t i,
	  data_t val) {
  assert(!is_iterator(heap, list));
  assert(0);
}

/* Positional remove */
void removeP(abstract_heapt *heap,
	     ptr_t list,
	     index_t i)  {
  assert(!is_iterator(heap, list));
  assert(0);
}

/*************************
 *  Iterator operators
 ************************/

void iterator(abstract_heapt* heap,
	      ptr_t it,
	      ptr_t list) {
  assert (is_iterator(heap, it) &&
	  !is_iterator(heap, list));

  node_t nlist = deref(heap, list);
  assign_ptr(heap, it, nlist);
}


/* Iterator add - add val before the iterator it */
void addI(abstract_heapt *heap,
	  ptr_t it,
	  data_t val) {

  assert (is_iterator(heap, it));

  // LSH FIXME: this case not supported yet so use assume
  assume (!is_null(heap, it));
  node_t nit = deref(heap, it);
  
  // create new node and set data
  node_t nnew = alloc(heap);
  assign_data(heap, nnew, val);

  // if the list was empty create new node
  // LSH FIXME: what if it was an iterator that reached null?
  /* if ( nit == null_node) { */
  /*   assign_succ(heap, nnew, null_node, 1); */
  /*   assign_ptr(heap, it, nnew); */
  /*   return; */
  /* } */

  //  prev_nit -----d-------> nit ---> null
  // to
  //  prev_nit -d-> nnew -1-> nit ---> null
  
  // nnew points to nit
  assign_succ(heap, nnew, nit, 1);
  node_t prev_nit = prev(heap, nit);
  // set the nprev that used to point to nit to point to nnew
  if (prev_nit != null_node) {
    assign_succ(heap, prev_nit, nnew, dist(heap, prev_nit));
    invalidate_prev(heap, nnew);
  }
  invalidate_succ(heap, nit);
}

/* Iterator set - sets the last value returned by next */
void setI(abstract_heapt *heap,
	  ptr_t it,
	  data_t val)  {

  assume (it < NPROG);
  assert (is_iterator(heap, it));
  
  node_t nx = deref(heap, it);
  
  // LSH FIXME: cannot get prev of null_node
  assume (nx != null_node);

  node_t nprev = prev(heap, nx);
  assert (nprev != null_node);
  
  assign_data(heap, nprev, val);
}


/* Iterator remove - removes the last value returned by next */
void removeI(abstract_heapt *heap,
	     ptr_t it)  {
  assume (it < NPROG);
  assert (is_iterator(heap, it));
  
  node_t nit = deref(heap, it);
  // FIXME: we cannot compute the prev of null currently 
  assume(nit != null_node);
  // the node we will be removing
  node_t nrem = prev(heap, nit);

  // it cannot point to the beggining of the list
  // (no previous element to remove)
  assert (nrem != null_node);

  // the node before the one we are removing
  node_t nprev = prev(heap, nrem);
  predicate_index_t pi;
  
  if (nprev == null_node) {
    // We are deleting the head of the list
    if (dist(heap, nrem) == 1) {
      // clear the node to be removed
      clear_node(heap, nrem);
      // invalidate all iterators pointing to it and
      // update lists to point to the new head
      invalidate_and_update(heap, nrem, nit);
      return;
    }
    
    word_t data;

    // update the predicates and assume constraints on the new value
    for (pi = 0; pi < NPREDS; ++pi) {
      // true universals are maintained
      if (get_univ(heap, nrem, pi) == bool_true) {
	assume(eval_pred(pi, data));
	assign_univ(heap, nrem, pi, bool_true);
      } else {
	assign_univ(heap, nrem, pi, bool_unknown);
      } 
      // false existentials are maintained
      if (get_exists(heap, nrem, pi) == bool_false) {
	assume(!eval_pred(pi, data));
	assign_exists(heap, nrem, pi, bool_false);
      } else {
	assign_exists(heap, nrem, pi, bool_unknown);
      }
    }
    assign_data(heap, nrem, data);
    assign_succ(heap, nrem, nit, dist(heap, nrem) - 1);
    invalidate(heap, nrem);
    return;
  }
  
  // we are deleting a node in the middle
  for (pi = 0; pi < NPREDS; ++pi) {
    bool_t new_univ = and (get_univ(heap, nprev, pi),
			   get_univ(heap, nrem, pi));
    bool_t new_exists =  or (get_exists(heap, nprev, pi),
			     get_exists(heap, nrem, pi));
    assign_univ(heap, nprev, pi, new_univ);
    assign_exists(heap, nprev, pi, new_exists);
    assign_succ(heap, nprev, nit, s_add(dist(heap, nprev), dist(heap, nrem)) - 1);
    clear_node(heap, nrem);
  }
}

/* Iterator next */
word_t next(abstract_heapt *heap,
	    ptr_t it) {
  assert (is_iterator(heap, it));
  
  assume(it < NPROG);

  node_t nit = deref(heap, it);
  assert (nit != null_node);

  word_t val = data(heap, nit);
  // subdivide creates new node at distance 1 and
  // updates predicates
  node_t succ_nit = subdivide(heap, nit);
  assign_ptr(heap, it, succ_nit);
  return val;
}

/* Iterator has next */
_Bool hasNext(abstract_heapt *heap,
	      ptr_t it) {
  assert (is_iterator(heap, it));
  return !is_null(heap, it);
}


/* Return the next index pointed to by iterator */
index_t nextIndex(abstract_heapt *heap,
		  ptr_t x) {
  assert(0);
  return -1;
}

