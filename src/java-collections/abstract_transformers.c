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
 * What is the value of the i_th existential predicate for n ?
 */
static bool_t exists(const abstract_heapt *heap,
		     node_t n,
		     predicate_index_t pi) {
  assume(n < NABSNODES);
  assume(pi < NPREDS);
  return heap->existenial[n][pi];
}

/*
 * What is the value of the i_th universal predicate for n ?
 */
static bool_t univ(const abstract_heapt *heap,
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

/*
 * x.n = y;
 *
 * x and y are nodes.
 */
static void destructive_assign_succ(abstract_heapt *heap,
                                    node_t x,
                                    node_t y,
                                    word_t dist) {
  assume(x < NABSNODES);
  assume(y < NABSNODES);
  heap->succ[x] = y;
  heap->dist[x] = dist;
}

static void destructive_assign_univ(abstract_heapt *heap,
				    node_t nx,
				    predicate_index_t pi,
				    bool_t pred_val) {
  assume(nx < NABSNODES);
  assume(pi < NPREDS);
  heap->universals[nx][pi] = pred_val;
}

static void destructive_assign_exists(abstract_heapt *heap,
				      node_t nx,
				      predicate_index_t pi,
				      bool_t pred_val) {
  assume(nx < NABSNODES);
  assume(pi < NPREDS);
  heap->exists[nx][pi] = pred_val;
}

/*
 * x = y;
 *
 * x and y are pointers.
 */
void abstract_assign(abstract_heapt *heap,
                     ptr_t x,
                     ptr_t y) {
  assume(x < NPROG);
  assume(y < NPROG);

  //copy_abstract(pre, post);

  node_t py = deref(heap, y);
  destructive_assign_ptr(heap, x, py);
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
  predicate_index_t pi = 0;
  for (pi = 0; pi < NPREDS; ++pi) {
    destructive_assign_unvis(heap, nx, pi, bool_unknown);
    destructive_assign_exists(heap, nx, pi, bool_unknown);
  }
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
    return nx_succ;
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
      // Only true universals are still true on the segments
      bool_t new_univ = univ(heap, nx, pi) == bool_true? bool_true : bool_unknown;
      // Only false existentials are still false on the segments
      bool_t new_exists = exists(heap, nx, pi) == bool_false ? bool_true : bool_unknown;

      // Update predicates for nx 
      destructive_assign_univ(heap, nx, pi, new_univ);
      destructive_assign_exists(heap, nx, pi, new_exists);
      // Update predicates for the newly allocated node nnew 
      destructive_assign_univ(heap, nnew, pi, new_univ);
      destructive_assign_exists(heap, nnew, pi, new_exists);
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

  // null doesn't have any data
  if (data(heap, null_node) != undef) {
    return 0;
  }

  predicate_index_t pi;
  // null predicates are all unknown
  for (pi = 0; pi < NPREDS; ++pi) {
    if (exists(heap, null_node, pi) != bool_unknown) {
      return 0;
    }
    
    if (univ(heap, null_node, pi) != bool_unknown) {
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
      bool_t e = exists(heap, n, pi);
      bool_t u = univ(heap, n, pi);
      
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

word_t alias(const abstract_heapt *heap,
             ptr_t x,
             ptr_t y) {
  node_t xn = deref(heap, x);
  node_t yn = deref(heap, y);

  return xn == yn;
}

word_t is_null(const abstract_heapt *heap,
               ptr_t x) {
  return deref(heap, x) == null_node;
}

bool_t exists(const abstract_heapt *heap,
	     ptr_t x,
	     ptr_t y,
	     predicate_index_t pi) {
  assert(is_path(heap, x, y));
  
  node_t nx = deref(heap, x);
  node_t ny = deref(heap, y);

  if (nx == null_node) {
    return bool_unknown;
  }

  // trying to be efficient?
  if (nx == ny) {
    return exists(heap, nx);
  }
  
  bool_t res = bool_false;
  word_t i;
  for (i = 0; i < NABSNODES; ++i) {
    if (nx == ny) {
      if (nx != null_node) {
	res = or(res, exists(heap, nx, pi));
      }
      return res;
    }
    res = or(res, exists(heap, nx, pi));
    nx = succ(heap, nx);
  }
  return bool_unknown;
}

bool_t forall(const abstract_heapt *heap,
	     ptr_t x,
	     ptr_t y,
	     predicate_index i) {
  assert(is_path(heap, x, y));
  
  node_t nx = deref(heap, x);
  node_t ny = deref(heap, y);

  if (nx == null_node) {
    return bool_unknown;
  }

  // trying to be efficient?
  if (nx == ny) {
    return univ(heap, nx);
  }
  
  bool_t res = bool_true;
  word_t i;
  for (i = 0; i < NABSNODES; ++i) {
    if (nx == ny) {
      if (nx != null_node) {
	res = and(res, univ(heap, nx));
      }
      return res;
    }
    res = and(res, univ(heap, nx));
    nx = succ(heap, nx);
  }
  return bool_unknown;
}

bool_t sorted(const abstract_heapt *heap,
	     ptr_t x,
	     ptr_t y) {
  assert(false);
  return false;
}


/*************************
 *
 *  Abstract accessors
 * 
 ************************/

/* Positional get */
data_t get(const abstract_heapt *heap,
	   ptr_t x,
	   index_t i) {
  assert(false);
  return 0;
}

/* Iterator get */
data_t get(const abstract_heapt *heap,
	   ptr_t x) {
  // non-deterministic value
  data_t val = nondet_data_t();
  // LSH TODO: finish
  
  /* node_t nx = deref(heap, x); */

  /* assert (nx != null_node); */
  
  /* _Bool preds = true; */
  /* word_t nx_dist = dist(heap, x); */
  /* predicate_index_t pi; */
  /* for (pi = 0; pi < NPREDS; ++pi) { */
  /*   bool_t univ = univ(heap, nx, pi); */
  /* } */
  /* if (nx_dist == 1) { */
  /*   for (pi = 0; pi < NPREDS; ++pi) { */
  /*     bool_t exists = exists(heap, nx, pi); */
  /*     res  */
  /*   } */
  /* } */
  /* // if distance is 1 assume all existentials */
  /* // assume all universals */
  
  /* assume(preds); */
  return val;
}

		 
/*************************
 *
 *  Abstract transformers
 * 
 ************************/

/* Positional set */
void set(abstract_heapt *heap,
	 ptr_t x,
	 index_t i,
	 data_t val) {
  assert(false);
}

/* Positional add (only one) */
void add(abstract_heapt *heap,
	 ptr_t x,
	 index_t i,
	 data_t val) {
  assert(false);
}

/* Positional remove */
void remove(abstract_heapt *heap,
	    ptr_t x,
	    index_t i) {
  assert(false);
}

void abstract_assign(abstract_heapt *heap,
                     ptr_t x,
                     ptr_t y) {
  assert(false);
}

/* Iterator set */
void set(abstract_heapt *heap,
	 ptr_t x,
	 data_t val) {

  assume(x < NPROG);
  
  node_t nx = deref(heap, x);
  assert (nx != null_node);

  subdivide(heap, nx);

  // Update predicates
  predicate_index_t pi;
  for (pi = 0; pi < NPREDS; ++pi) {
    _Bool val_pred = eval_pred(pi, val);
    destructive_assign_univ(heap, nx, pi, bool_t(val_pred));
    destructive_assign_exists(heap, nx, pi, bool_t(val_pred));
  }
}

/* Iterator next */
void next(abstract_heapt *heap,
	  ptr_t x) {
  assume(x < NPROG);

  node_t nx = deref(heap, x);
  assert (nx != null_node);  
  // subdivide creates new node at distance 1 and
  // updates predicates
  node_t succ_nx = subdivide(heap, nx);
 
  destructive_assign_ptr(heap, x, succ_nx);
}

/* Iterator has succ */
_Bool has_next(abstract_heapt *heap,
	       ptr_t x) {

  node_t nx = deref(heap, x);
  word_t nx_dist = dist(heap, x);
  assert ( nx != null_node);
  return nx_dist > 1 || succ(heap, nx) != null_node;
}
