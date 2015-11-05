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
  return heap->ptr[p];
}

/*
 * Succ operator -- which node is in n's succ pointer?
 */
static node_t succ(const abstract_heapt *heap,
                   node_t n) {
  // Ensure n is an allocated node.
  assume(n < NABSNODES);
  assert (!invalid_node(n));
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
  assert (!invalid_node(n));
  return heap->prev[n];
}


/*
 * How far away is n's successor?
 */
static word_t dist(const abstract_heapt *heap,
                   node_t n) {
  assume(n < NABSNODES);
  assert (!invalid_node(n));
  return heap->dist[n];
}

/*
 * How far away is n's successor?
 */
static word_t data(const abstract_heapt *heap,
                   node_t n) {
  assume(n < NABSNODES);
  assert(n != null_node);
  assert (!invalid_node(n));
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
  assert (!invalid_node(n));
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
  assert (!invalid_node(n));
  return heap->universal[n][pi];
}

/*
 * What is the value of the i_th universal predicate for n ?
 */
static _Bool invalid_node(const abstract_heapt *heap,
			  node_t n) {
  assume(n < NABSNODES);
  return heap->succ[n] == INVALID;
}

static _Bool eval_pred(predicate_index_t pi, data_t val) {
  assume(pi < NPREDS);
  return predicates[pi](val);
}

/*
 * x = n;
 *
 * x is a pointer, n is a graph node.
 */
static void destructive_assign_ptr(abstract_heapt *heap,
                                   ptr_t x,
                                   node_t n) {
  assume(x < NPROG);
  assume(n < NABSNODES);
  heap->ptr[x] = n;
}

static void destructive_assign_univ(abstract_heapt *heap,
				    node_t nx,
				    predicate_index_t pi,
				    bool_t pred_val) {
  assume(nx < NABSNODES);
  assume(pi < NPREDS);
  heap->universal[nx][pi] = pred_val;
}

static void destructive_assign_exists(abstract_heapt *heap,
				      node_t nx,
				      predicate_index_t pi,
				      bool_t pred_val) {
  assume(nx < NABSNODES);
  assume(pi < NPREDS);
  heap->existential[nx][pi] = pred_val;
}


static void destructive_assign_succ(abstract_heapt *heap,
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
      destructive_assign_univ(heap, x, pi, bool_true);
      destructive_assign_exists(heap, x, pi, bool_true);
    }
  }
}

static void destructive_assign_data(abstract_heapt *heap,
                                    node_t x,
                                    data_t val) {
  assume(x < NABSNODES);
  assert (x != null_node);
  heap->data[x] = val;
}

/*
 * Allocate a new node.
 */
static node_t destructive_alloc(abstract_heapt *heap) {
  node_t n;
  assume(heap->nnodes < NABSNODES);
  return heap->nnodes++;
}


/*
 * Mark node as invalid (for remove and invalidating iterators).
 */
static void destructive_invalidate(abstract_heapt *heap,
				   node_t nx) {
  assert (nx != null_node);
  assert (nx < heap->nnodes);
  heap->succ[nx] = INVALID;
  heap->prev[nx] = INVALID;
}

/*
 * x = new();
 */
void abstract_new(abstract_heapt *heap,
                  ptr_t x) {
  assume(x < NPROG);

  // Just allocate a new node and have x point to it.
  node_t nx = destructive_alloc(heap);
  destructive_assign_succ(heap, nx, null_node, 1);
  destructive_assign_ptr(heap, x, nx);
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
    node_t nnew = destructive_alloc(heap);
    word_t new_dist = s_sub(nx_dist, 1);
    predicate_index_t pi;
    for (pi = 0; pi < NPREDS; ++pi) {
      bool_t new_univ = get_univ(heap, nx, pi);
      bool_t new_exists = get_exists(heap, nx, pi);
      // Assume the predicates for the values stored at nnew
      // Only true universals are still true on the data
      if (new_univ == bool_true) {
	// assume(eval_pred(pi, data(heap, nx)));
	assume(eval_pred(pi, data(heap, nnew)));
      } 
      // Only false existentials are still false on the data
      if (get_exists == bool_false) {
	// assume(!eval_pred(pi, data(heap, nx)));
	assume(!eval_pred(pi, data(heap, nnew)));
      }

      // Update predicates for the newly allocated node nnew
      // (if dist is 1 they vacuously hold)
      if (new_dist > 1) {
	destructive_assign_univ(heap, nnew, pi, new_univ);
	destructive_assign_exists(heap, nnew, pi, new_exists);
      }
    }

    // Reassign nnew's succ pointer to nx's successor succ_nx
    destructive_assign_succ(heap, nnew, succ_nx, new_dist);
    // Reassign nx's succ pointer to the newly allocated node.
    destructive_assign_succ(heap, nx, nnew, 1);
    return nnew;
  }
}

/*
  Invalidate all the pointers from nx to null (excluding)
 */
extern void smoothen_succ(abstract_heapt* heap,
			  node_t nx) {
  assert (nx != null_node);

  node_t initial_nx = nx;
  
  nx = succ(heap, nx);

  word_t i;
  bool_t new_univs[NPREDS];
  bool_t new_exists[NPREDS];

  for (pi = 0; pi < NPREDS; ++pi) {
    new_univs[pi] = bool_true;
    new_exists[pi] = bool_false;
  }
  
  predicate_index_t pi;
  for (i = 1; i < NABSNODES; ++i) {
    if (nx == null_node)
      return;
    // compute new information
    for (pi = 0; pi < NPREDS; ++pi) {
      // for each predicate collect data stored at node and on edge
      new_univ[pi] = and (and (new_univ[pi], get_univ(heap, nx, pi)),
			  eval_pred(pi, data(nx, pi)));
      new_exists[pi] = or (or (new_exists[pi], get_exists(heap, nx, pi)),
			   eval_pred(pi, data(nx, pi)));
    }
    node_t old = nx;
    nx = succ(heap, nx);
    destructive_invalidate(heap, old);
  }
  
  // update the predicate values for the initial node
  for (pi = 0; pi < NPREDS; ++pi) {
    destructive_assign_univ(heap, initial_nx, pi, new_univs[pi]);
    destructive_assign_exists(heap, initial_nx, pi, new_exists[pi]);
  }
}

/*
  Invalidate all the pointers from beginning of list to nx (excluding)
 */
extern void smoothen_prev(abstract_heapt* heap,
			  node_t nx) {
  assert (nx != null_node);

  node_t initial_nx = nx;
  
  nx = prev(heap, nx);

  word_t i;
  bool_t new_univs[NPREDS];
  bool_t new_exists[NPREDS];

  for (pi = 0; pi < NPREDS; ++pi) {
    new_univs[pi] = bool_true;
    new_exists[pi] = bool_false;
  }
  
  predicate_index_t pi;
  for (i = 1; i < NABSNODES; ++i) {
    // we want to exclude the first pointer
    if (prev(heap, nx) == null_node)
      return;
    // compute new information
    for (pi = 0; pi < NPREDS; ++pi) {
      // for each predicate collect data stored at node and on edge
      new_univ[pi] = and (and (new_univ[pi], get_univ(heap, nx, pi)),
			  eval_pred(pi, data(nx, pi)));
      new_exists[pi] = or (or (new_exists[pi], get_exists(heap, nx, pi)),
			   eval_pred(pi, data(nx, pi)));
    }
    node_t old = nx;
    nx = prev(heap, nx);
    destructive_invalidate(heap, old);
  }
  
  // update the predicate values for the initial node
  for (pi = 0; pi < NPREDS; ++pi) {
    destructive_assign_univ(heap, initial_nx, pi, new_univs[pi]);
    destructive_assign_exists(heap, initial_nx, pi, new_exists[pi]);
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
  if (deref(heap, null_ptr) != null_node) {
    return 0;
  }

  // The null node doesn't point anywhere and
  // by convention has no predecessor.
  if (succ(heap, null_node) != null_node ||
      prev(heap, null_node) != null_node) {
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
  is_named[0] = 1;
  
  for (p = 1; p < NPROG; p++) {
    n = deref(heap, p);
    is_named[n] = 1;
    
    // only allocated nodes
    if (n >= heap->nnodes) {
      return 0;
    }

    m = succ(heap, n);
    if (m != null_node) {
      // check that named nodes have succ n + 1
      if (n + 1 != m)
	  return 0;
      // and the predecessor points back
      if (prev(heap, m) != n)
	return 0;
      has_in_edge[m] = 1;
    }

    if (invalid_node(heap, n))
      return 0;
        
    for (pi = 0; pi < NPREDS; ++pi) {
      bool_t e = get_exists(heap, n, pi);
      bool_t u = get_univ(heap, n, pi);

      // edges of length 1 have the predicates true
      if (dist(heap, n) == 1 &&
	  (e != bool_true || u != bool_true))
	return 0;
      
      if (e > bool_unknown || u > bool_unknown)
	return 0;
      
      // predicates are known for all nodes 
      if (e == bool_unknown ||
	  u == bool_unknown) {
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

  // check that all nodes without incoming edges have prev(x) == null
  for (i = 0; i < NABSNODES; ++i) {
    if (has_in_edge[i] == 0 && heap->prev[i] != null_node)
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

    curr_dist = s_add(curr_dist, dist(heap, n));
    n = succ(heap, n);
  }

  return INF;
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
    return bool_true;
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
	   ptr_t x,
	   index_t i) {
  assert(0);
  return 0;
}

/* Iterator get */
data_t getI(const abstract_heapt *heap,
	    ptr_t x) {
  node_t nx = deref(heap, x);
  assert (nx != null_node);
  return data(heap, nx);
}

		 
/*************************
 *
 *  Abstract transformers
 * 
 ************************/

/* Adds element at end of list */
void add(abstract_heapt *heap,
	 ptr_t x,
	 data_t val) {
  node_t nx = deref(heap, x);
  
  if ( nx == null_node) {
    abstract_new(heap, x);
    nx = deref(heap, x);
    destructive_assign_data(heap, nx, val);
    return;
  }

  smoothen_succ(heap, nx);
  
  word_t i;
  for (i = 0; i < NABSNODES; ++i) {
    if (succ(heap, nx) == null_node) {
      node_t nnew = destructive_alloc(heap);
      destructive_assign_succ(heap, nnew, null_node, dist(heap, nx));      
      destructive_assign_succ(heap, nx, nnew, 1);
    }
    nx = succ(heap, nx);
  }
  return;
}

void assign(abstract_heapt *heap,
	    ptr_t x,
	    ptr_t y) {
  assume(x < NPROG);
  assume(y < NPROG);

  //copy_abstract(pre, post);

  node_t py = deref(heap, y);
  destructive_assign_ptr(heap, x, py);
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
	  ptr_t x,
	  index_t i,
	  data_t val) {
  assert(0);
}


/* Positional add */
void addP(abstract_heapt *heap,
	  ptr_t x,
	  index_t i,
	  data_t val) {
  assert(0);
}

/* Positional remove */
void removeP(abstract_heapt *heap,
	     ptr_t x,
	     index_t i)  {
  assert(0);
}

/*************************
 *  Iterator operators
 ************************/

/* Iterator add */
void addI(abstract_heapt *heap,
	  ptr_t x,
	  data_t val) {

  node_t nx = deref(heap, x);
  
  // create new node and set data
  node_t nnew = destructive_alloc(heap);
  destructive_assign_data(heap, nnew, val);

  // if the list was empty create new node
  // LSH FIXME: what if x was an iterator that reached null?
  if ( nx == null_node) {
    destructive_assign_succ(heap, nnew, null_node, 1);
    destructive_assign_ptr(heap, x, nnew);
    return;
  }

  //  prev_nx -----d-------> nx ---> null
  // to
  //  prev_nx -d-> nnew -1-> nx ---> null
  
  // nnew points to nx
  destructive_assign_succ(heap, nnew, nx, 1);
  node_t prev_nx = prev(heap, nx);
  // set the nprev that used to point to nx to point to nnew
  if (prev_nx != null_node) {
    destructive_assign_succ(heap, prev_nx, nnew, dist(heap, prev_nx));
    smoothen_prev(heap, nnew);
  }
  smoothen_succ(heap, nx);
}

// LSH FIXME: this is not the actual Java semantics (in Java it sets the
// last value returned!), same for remove
/* Iterator set */
void setI(abstract_heapt *heap,
	  ptr_t x,
	  data_t val)  {
  assume(x < NPROG);
  
  node_t nx = deref(heap, x);
  assert (nx != null_node);

  destructive_assign_data(heap, nx, val);
}


// TODO: remove smoothen, just invalidate pointers
// add mark for what is iterator and what is list
// 

/* Iterator remove */
void removeI(abstract_heapt *heap,
	     ptr_t x)  {
  assume (x < NPROG);
  node_t nx = deref(heap, x);

  assert (nx != null_node);
  
  node_t succ_nx = succ(heap, nx);
  node_t prev_nx = prev(heap, nx);

  if (prev_nx == null_node) {
    destructive_assign_succ(heap, prev_nx, succ_nx);
  }
  
  assert(0);
}

/* Iterator next */
word_t next(abstract_heapt *heap,
	    ptr_t x) {
  assume(x < NPROG);

  node_t nx = deref(heap, x);
  assert (nx != null_node);

  word_t valx = data(heap, nx);
  // subdivide creates new node at distance 1 and
  // updates predicates
  node_t succ_nx = subdivide(heap, nx);
  destructive_assign_ptr(heap, x, succ_nx);
  return valx;
}

/* Return the next index pointed to by iterator */
index_t nextIndex(abstract_heapt *heap,
		  ptr_t x) {
  assert(0);
  return -1;
}

