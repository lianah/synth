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

  // assert(heap->nnodes < NABSNODES);
  assume(heap->nnodes < NABSNODES);
  return heap->nnodes++;
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
  /* predicate_index_t pi = 0; */
  /* for (pi = 0; pi < NPREDS; ++pi) { */
  /*   destructive_assign_univ(heap, nx, pi, bool_unknown); */
  /*   destructive_assign_exists(heap, nx, pi, bool_unknown); */
  /* } */
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
 * Check that the heap is well formed.
 */
_Bool valid_abstract_heap(const abstract_heapt *heap) {
  // NULL points to the null node.
  if (deref(heap, null_ptr) != null_node) {
    return 0;
  }

  // The null node doesn't point anywhere.
  if (succ(heap, null_node) != null_node) {
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

  word_t nreachable = 0;

  ptr_t p;
  node_t n, m;
  word_t i;
  predicate_index_t pi; 

  for (p = 0; p < NPROG; p++) {
    n = deref(heap, p);
    is_named[n] = 1;
    
    // only allocated nodes
    if (n >= heap->nnodes) {
      return 0;
    }

    // check that named nodes have succ n + 1
    if (succ(heap, n) != null_node &&
	n + 1 != succ(heap, n)) {
      return 0;
    }

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
	 data_t val);

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

/* Iterator remove */
void removeI(abstract_heapt *heap,
	     ptr_t x)  {
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

