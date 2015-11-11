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

void debug_assert (_Bool x, char* tag) {
  if(!x) {
    printf("\n%s\n", tag);
  }
  assert(x);
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
  Assume(p < NPROG);
  Assert (heap->ptr[p] != INVALID, "INV_ERROR: deref");
  return heap->ptr[p];
}

/*
 * Check if p is an iterator. 
 */
static _Bool is_iterator(const abstract_heapt *heap,
			 ptr_t p) {
  // Ensure p is a real pointer.
  Assume(p < NPROG);
  return heap->is_iterator[p];
}


/*
 * Succ operator -- which node is in n's succ pointer?
 */
static node_t succ(const abstract_heapt *heap,
                   node_t n) {
  // Ensure n is an allocated node.
  Assume(n < NABSNODES);
  return heap->succ[n];
}

/*
 * Prev operator -- which node is in n's predecessor pointer?
 */
static node_t prev(const abstract_heapt *heap,
                   node_t n) {
  // Ensure n is an allocated node.
  Assume(n < NABSNODES);
  Assert(n != null_node, "INV_ERROR: prev");
  return heap->prev[n];
}


/*
 * How far away is n's successor?
 */
static word_t dist(const abstract_heapt *heap,
                   node_t n) {
  Assume(n < NABSNODES);
  return heap->dist[n];
}

/*
 * How far away is n's successor?
 */
static word_t data(const abstract_heapt *heap,
                   node_t n) {
  Assume(n < NABSNODES);
  Assert(n != null_node, "INV_ERROR: data");
  return heap->data[n];
}


/*
 * What is the value of the i_th existential predicate for n ?
 */
/* static bool_t get_exists(const abstract_heapt *heap, */
/* 			 node_t n, */
/* 			 predicate_index_t pi) { */
/*   Assume(n < NABSNODES); */
/*   Assume(pi < NPREDS); */
/*   return heap->existential[n][pi]; */
/* } */

/*
 * What is the value of the sorted predicate for n ?
 */
static bool_t get_sorted(const abstract_heapt *heap,
			 node_t n) {
  Assume(n < NABSNODES);
  return heap->sorted[n];
}

/*
 * What is the value of the max elem for n ?
 */
static data_t get_max(const abstract_heapt *heap,
			 node_t n) {
  Assume(n < NABSNODES);
  return heap->max[n];
}

/*
 * What is the value of the min elem for n ?
 */
static data_t get_min(const abstract_heapt *heap,
			 node_t n) {
  Assume(n < NABSNODES);
  return heap->min[n];
}


/*
 * What is the value of the i_th universal predicate for n ?
 */
static bool_t get_univ(const abstract_heapt *heap,
		       node_t n,
		       predicate_index_t pi) {
  Assume(n < NABSNODES);
  Assume(pi < NPREDS);
  return heap->universal[n][pi];
}

/*
 * What is the value of the i_th universal predicate for n ?
 */
static _Bool eval_pred(predicate_index_t pi, data_t val) {
  Assume(pi < NPREDS);
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
  Assume(x < NPROG);
  Assume(n < NABSNODES);
  heap->ptr[x] = n;
}

static void assign_univ(abstract_heapt *heap,
			node_t nx,
			predicate_index_t pi,
			bool_t pred_val) {
  Assume(nx < NABSNODES);
  Assume(pi < NPREDS);
  heap->universal[nx][pi] = pred_val;
}

static void assign_sorted(abstract_heapt *heap,
			node_t nx,
			predicate_index_t pi,
			bool_t sorted_val) {
  Assume(nx < NABSNODES);
  Assume(pi < NPREDS);
  heap->sorted[nx] = sorted_val;
}

static void assign_min_max(abstract_heapt *heap,
			node_t nx,
			predicate_index_t pi,
			data_t min_val,
			data_t max_val) {
  Assume(nx < NABSNODES);
  Assume(pi < NPREDS);
  heap->min[nx] = min_val;
  heap->max[nx] = max_val;
}



/* static void assign_exists(abstract_heapt *heap, */
/* 			  node_t nx, */
/* 			  predicate_index_t pi, */
/* 			  bool_t pred_val) { */
/*   Assume(nx < NABSNODES); */
/*   Assume(pi < NPREDS); */
/*   heap->existential[nx][pi] = pred_val; */
/* } */


static void assign_succ(abstract_heapt *heap,
			node_t x,
			node_t y,
			word_t dist) {
  Assume(x < NABSNODES);
  Assume(y < NABSNODES);
  
  heap->succ[x] = y;
  heap->prev[y] = x;
  
  heap->dist[x] = dist;
  
  predicate_index_t pi = 0;
  if (dist == 0) {
    for (pi = 0; pi < NPREDS; ++pi) {
      assign_univ(heap, x, pi, bool_true);
      // Cris TODO: check this
      assign_sorted(heap, x, pi, bool_true);
    }
  }
}

static void assign_data(abstract_heapt *heap,
			node_t x,
			data_t val) {
  Assume(x < NABSNODES);
  Assert (x != null_node, "INV_ERROR");
  heap->data[x] = val;
}

/*
 * Allocate a new node.
 */
static node_t alloc(abstract_heapt *heap) {
  node_t n;
  Assume(heap->nnodes < NABSNODES);
  return heap->nnodes++;
}


/*
 * Mark node as invalid (for remove and invalidating iterators).
 */
static void invalidate(abstract_heapt *heap,
		       node_t nx) {
  Assert (nx != null_node, "INV_ERROR");
  Assert (nx < heap->nnodes, "INV_ERROR");
  word_t i;
  for (i = 0; i < NPROG; ++i) {
    if (is_iterator(heap, i) &&
	heap->ptr[i] == nx) {
      heap->ptr[i] = INVALID;
    }
  }
}

static void update_ptr(abstract_heapt *heap,
		       node_t nx,
		       node_t nnew) {
  Assert (nx != null_node, "INV_ERROR");
  Assert (nx < heap->nnodes, "INV_ERROR");
  word_t i;
  for (i = 0; i < NPROG; ++i) {
    if (heap->ptr[i] == nx) {
      if (heap->is_iterator[i] == 0) {
	// lists now point to the new node
	heap->ptr[i] = nnew;
      }
    }
  }
}

/*
 * Mark node as invalid (for remove and invalidating iterators).
 */
static void invalidate_and_update(abstract_heapt *heap,
				  node_t nx,
				  node_t nnew) {
  Assert (nx != null_node, "INV_ERROR");
  Assert (nx < heap->nnodes, "INV_ERROR");
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
  Assert (nx != null_node, "INV_ERROR");
  Assert (nx < heap->nnodes, "INV_ERROR");
  word_t data;
  assign_data(heap, nx, data);
  assign_succ(heap, nx, null_node, 0);
}

/*
 * x = new();
 */
void abstract_new(abstract_heapt *heap,
                  ptr_t x) {
  Assume(x < NPROG);

  // Just allocate a new node and have x point to it.
  node_t nx = alloc(heap);
  assign_succ(heap, nx, null_node, 0);
  assign_ptr(heap, x, nx);
}


/*
  Creates a new node nnew at distance 1 from nx and
  updates the predicates, succ and len for nx, and nnew  
*/
node_t subdivide(abstract_heapt *heap,
		 node_t nx) {
  Assert (nx < NABSNODES, "INV_ERROR");
  node_t succ_nx = succ(heap, nx);
  word_t nx_dist = dist(heap, nx);

  // Two cases: 
  //
  // (1): x has a direct successor, i.e. x -1> succ_nx
  // (2): x's successor is some distance > 1 away, i.e. x -k-> succ_nx
  if (nx_dist == 0) {
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
    // nx -0-> nnew -(k-1)-> succ_nx
    //
    // Begin by allocating a new node between nx and succ_nx.
    node_t nnew = alloc(heap);
    word_t new_dist = s_sub(nx_dist, 1);
    predicate_index_t pi;
    for (pi = 0; pi < NPREDS; ++pi) {
      bool_t new_univ = get_univ(heap, nx, pi);
      //bool_t new_exists = get_exists(heap, nx, pi);
      // Assume the predicates for the values stored at nnew
      // Only true universals are still true on the data
      if (new_univ == bool_true) {
	Assume(eval_pred(pi, data(heap, nnew)));
	assign_univ(heap, nnew, pi, bool_true);
      } else {
	assign_univ(heap, nnew, pi, bool_unknown);
      }

      // Only false existentials are still false on the data
      /* if (get_exists == bool_false) { */
      /* 	Assume(!eval_pred(pi, data(heap, nnew))); */
      /* 	assign_exists(heap, nnew, pi, bool_false); */
      /* } else { */
      /* 	assign_exists(heap, nnew, pi, bool_unknown); */
      /* } */
    }

    // Reassign nnew's succ pointer to nx's successor succ_nx
    assign_succ(heap, nnew, succ_nx, new_dist);
    // Reassign nx's succ pointer to the newly allocated node.
    assign_succ(heap, nx, nnew, 0);
    return nnew;
  }
}

/*
  Invalidate all the pointers from nx to null (excluding)
*/
extern void invalidate_succ(abstract_heapt* heap,
			    node_t nx) {
  Assert (nx != null_node, "INV_ERROR");

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
  Assert (nx != null_node, "INV_ERROR");

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
  return bool_unknown;
}

/*
 * Compute the value of exists pi on path (nx, ny)
 */
/* static bool_t path_exists(const abstract_heapt *heap, */
/* 			  node_t nx, */
/* 			  node_t ny, */
/* 			  predicate_index_t pi) { */
/*   // This is technically the empty list so nothing exists */
/*   if (nx == ny) { */
/*     return bool_false; */
/*   } */

/*   bool_t res = bool_false; */
/*   word_t i; */
/*   for (i = 0; i < NABSNODES; ++i) { */
/*     if (nx == ny) { */
/*       return res; */
/*     } */
/*     res = or (res, (bool_t)eval_pred(pi, data(heap, nx))); */
/*     res = or(res, get_exists(heap, nx, pi)); */
/*     nx = succ(heap, nx); */
/*   } */
/*   return bool_unknown; */
/* } */



static void assume_consistent_node(const abstract_heapt *heap,
			      node_t nx) {
  if (nx == null_node)
    return;

  // witnesses for the negated universals (i.e. existentials)
  data_t vals[NPREDS];
  
  // we can only have as many witnesses as the length
  // we only need as many as predicates since each val is unconstrained 
  word_t num_nodes = dist(heap, nx);

  word_t pi, j;

  // indicates that there are no negated predicates

  for (pi = 0; pi < NPREDS; ++pi) {
    _Bool no_neg = 1;
    _Bool neg = 0;
    if (get_univ(heap, nx, pi) == bool_true) {
      // we Assume the positive predicates hold on all the witness values
      for (j = 0; j < NPREDS; ++j) {
	
	if (j >= num_nodes)
	  continue;
#ifdef __CPROVER
	Assume(eval_pred(pi, vals[j]));
#endif	
      }
    } else if (get_univ(heap, nx, pi) == bool_false) {
      // we check that each negative predicates (existentials) holds
      // for at least one value
      for (j = 0; j < NPREDS; ++j) {
	if (j >= num_nodes)
	  continue;
	neg = neg || !eval_pred(pi, vals[j]);
	no_neg = 0;
      }
    }
#ifdef __CPROVER    
    Assume(no_neg || neg);
#endif    
  }
  
}


static void assume_consistent(const abstract_heapt *heap) {
  word_t i;
  for (i = 0; i < NPROG; ++i) {
    assume_consistent_node(heap, deref(heap, i));
  }
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
      bool_t u = get_univ(heap, n, pi);
      bool_t s = get_sorted(heap, n);

      // edges of length 1 have the predicates true and are sorted
      if (n!= null_node &&
	  dist(heap, n) == 0 &&
	  (u != bool_true || s != bool_true))
	return 0;
      
      if (u > bool_unknown || s > bool_unknown)
	return 0;
      
      // predicates are known for all nodes 
      if (n != null_node &&
	  (u == bool_unknown || 
	   s == bool_unknown)) {
	return 0;
      }

      // Cris TODO: change dist to 0 after pulling Liana's changes -- done
      // enforce min <= max for all edges
      if (dist(heap, n) > 0 && get_min(heap, n) > get_max(heap, n)) {
	return 0;
      }
    }
  }

  // check that all nodes are named
  for (i = 0; i < NABSNODES-1; i++) {
    nreachable += is_named[i];
    if (is_named[i] && !is_named[succ(heap, i)]) {
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
    if (has_in_edge[i] == 0 &&
    	heap->prev[i] != null_node)
      return 0;
  }
  
  // If we're a fully reduced graph, we don't have any unreachable nodes.
  if (heap->nnodes != nreachable) {
    return 0;
  }

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
  if (heap->succ[null_node] != null_node ||
      heap->prev[null_node] != null_node) {
    return 0;
  }

  if (dist(heap, null_node) != 0) { 
    return 0;
  }

  predicate_index_t pi;
  // null predicates are all unknown
  for (pi = 0; pi < NPREDS; ++pi) {
    if (get_univ(heap, null_node, pi) != bool_unknown) {
      return 0;
    }
  }

  if (!is_minimal(heap))
    return 0;
  assume_consistent(heap);
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
    // count current node as well
    curr_dist = s_add(1, s_add(curr_dist, dist(heap, n)));
    n = succ(heap, n);
  }
  
  Assert (0, "INV_ERROR");
  return INF;
}

_Bool is_path(const abstract_heapt *heap,
	       ptr_t x,
	       ptr_t y) {
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
  Assert (0, "INV_ERROR");
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


/* _Bool exists_assume(const abstract_heapt *heap, */
/* 		    ptr_t x, */
/* 		    ptr_t y, */
/* 		    predicate_index_t pi) { */
/*   Assume(is_path(heap, x, y)); */
  
/*   node_t nx = deref(heap, x); */
/*   node_t ny = deref(heap, y); */
/*   return path_exists(heap, nx, ny, pi) == bool_true; */
/* } */

/* bool_t exists(const abstract_heapt *heap, */
/* 	      ptr_t x, */
/* 	      ptr_t y, */
/* 	      predicate_index_t prop) { */
/*   Assume(is_path(heap, x, y)); */
  
/*   node_t nx = deref(heap, x); */
/*   node_t ny = deref(heap, y); */

/*   if (nx == ny) */
/*     return bool_false; */

/*   predicate_index_t pi; */

/*   data_t val = nondet_data_t(); */
/*   _Bool check = eval_pred(prop, val); */
  
/*   for (pi = 0; pi < NPREDS; ++pi) { */
/*     bool_t pred = path_exists(heap, nx, ny, pi); */
/*     // Checking \/ (P_i (val) => prop(val)) */
/*     if (pred == bool_true) { */
/*       check = check || !eval_pred(pi, val); */
/*     } */
/*   } */
/*   return check ? bool_true : bool_unknown; */
/* } */


_Bool forall_assume(const abstract_heapt *heap,
		    ptr_t x,
		    ptr_t y,
		    predicate_index_t pi) {
  Assume(is_path(heap, x, y));
  node_t nx = deref(heap, x);
  node_t ny = deref(heap, y);
  return path_forall(heap, nx, ny, pi) == bool_true;
}

bool_t forall(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y,
	      predicate_index_t prop) {
  // LSH think about it!
  Assume(is_path(heap, x, y));
  
  node_t nx = deref(heap, x);
  node_t ny = deref(heap, y);

  if (nx == ny)
    return bool_true;
  
  predicate_index_t pi;

  data_t val = nondet_data_t();

  _Bool prop_val = eval_pred(prop, val);

  _Bool assumps = 1;
  
  for (pi = 0; pi < NPREDS; ++pi) {
    bool_t pred = path_forall(heap, nx, ny, pi);
    if (pred == bool_true) {
      assumps = assumps && eval_pred(pi, val);
    } else if (pred == bool_false) {
      // check if !pi => !prop
      // LSH FIXME: double check this is correct
      if (eval_pred(pi, val) || eval_pred(prop, val))
	return bool_false;
    }
  }


  if (!assumps || prop_val)
    return bool_true;
  if (!assumps || !prop_val)
    return bool_false;
  return bool_unknown;
}

bool_t sorted(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y) {

  Assume(is_path(heap, x, y));
  
  node_t nx = deref(heap, x);
  node_t ny = deref(heap, y);

  // This is technically the empty list so everything holds
  if (nx == ny) {
    return bool_true;
  }

  data_t prev_max = data(heap, nx);
  bool_t res = bool_true;
  word_t i;

  for (i = 0; i < NABSNODES; ++i) {
    if (nx == ny) {
      return res;
    }

    res = and(res, prev_max <= data(heap, nx));
    prev_max = data(heap, nx);
    res = and(res, get_sorted(heap, nx));
    // if len > 0 then we must also consider the values of the abstracted segment
    if(dist(heap, nx) > 0) {
      res = and(res, prev_max <= get_min(heap, nx));
      prev_max = get_max(heap, nx);
    }

    nx = succ(heap, nx);
  }

  // LSH FIXME: paper actually checks entailment
  return bool_unknown;

  Assert(0, "INV_ERROR");
  return 0;
}

data_t min(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y) {

  Assume(is_path(heap, x, y));
    
  node_t nx = deref(heap, x);
  node_t ny = deref(heap, y);
 
  Assert(nx != ny, "MIN_FOR_EMPTY_SEG_ERR");

  word_t i;
  data_t curr_min = data(heap, nx);

  for (i = 0; i < NABSNODES; ++i) {
    if (nx == ny) {
      return curr_min;
    }

    if (data(heap, nx) < curr_min)
      curr_min = data(heap, nx);
    // if len > 0 then we must also consider the values of the abstracted segment
    if(dist(heap, nx) > 0) {
      if (get_min(heap, nx) < curr_min) {
	curr_min = get_min(heap, nx);
      }
    }

    nx = succ(heap, nx);
  }

  // LSH FIXME: paper actually checks entailment
  return bool_unknown;

  Assert(0, "INV_ERROR");
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
  Assert (!is_iterator(heap, list), "INV_ERROR");
  Assert(0, "INV_ERROR");
  return 0;
}

/* Iterator get */
data_t getI(const abstract_heapt *heap,
	    ptr_t it) {
  Assert (is_iterator(heap, it), "INV_ERROR");
  node_t nit = deref(heap, it);
  Assert (nit != null_node, "INV_ERROR");
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
  
  Assert (!is_iterator(heap, list), "INV_ERROR");
  node_t nlist = deref(heap, list);
  
  if ( nlist == null_node) {
    abstract_new(heap, list);
    nlist = deref(heap, list);
    assign_data(heap, nlist, val);
    return;
  }

  //invalidate_succ(heap, nlist);
  
  word_t i;
  for (i = 0; i < NABSNODES; ++i) {
    if (succ(heap, nlist) == null_node) {
      node_t nnew = alloc(heap);
      assign_succ(heap, nnew, null_node, 0);      
      assign_succ(heap, nlist, nnew, dist(heap, nlist));
      assign_data(heap, nnew, val);
      break;
    }
    nlist = succ(heap, nlist);
  }

  return;
}

void assign(abstract_heapt *heap,
	    ptr_t x,
	    ptr_t y) {
  Assume(x < NPROG);
  Assume(y < NPROG);

  Assert (is_iterator(heap, x) == is_iterator(heap, y), "INV_ERROR");

  node_t py = deref(heap, y);
  assign_ptr(heap, x, py);
}

/* Removes all elements from list */
void clear(abstract_heapt *heap,
	   ptr_t x) {
  Assert(0, "INV_ERROR");
}

/*************************
 *  Positional operators
 ************************/


/* Positional set */
void setP(abstract_heapt *heap,
	  ptr_t list,
	  index_t i,
	  data_t val) {
  Assert(!is_iterator(heap, list), "INV_ERROR");
  Assert(0, "INV_ERROR");
}


/* Positional add */
void addP(abstract_heapt *heap,
	  ptr_t list,
	  index_t i,
	  data_t val) {
  Assert(!is_iterator(heap, list), "INV_ERROR");
  Assert(0, "INV_ERROR");
}

/* Positional remove */
void removeP(abstract_heapt *heap,
	     ptr_t list,
	     index_t i)  {
  Assert(!is_iterator(heap, list), "INV_ERROR");
  Assert(0, "INV_ERROR");
}

/*************************
 *  Iterator operators
 ************************/

void iterator(abstract_heapt* heap,
	      ptr_t it,
	      ptr_t list) {
  Assert (is_iterator(heap, it) &&
	  !is_iterator(heap, list), "INV_ERROR");

  node_t nlist = deref(heap, list);
  assign_ptr(heap, it, nlist);
}


/* Iterator add - add val before the iterator it */
void addI(abstract_heapt *heap,
	  ptr_t it,
	  data_t val) {

  Assert (is_iterator(heap, it), "INV_ERROR");

  // LSH FIXME: this case not supported yet so use assume
  Assume (!is_null(heap, it));
  node_t nit = deref(heap, it);
  
  // create new node and set data
  node_t nnew = alloc(heap);
  assign_data(heap, nnew, val);

  // if the list was empty create new node
  // LSH FIXME: what if it was an iterator that reached null?
  /* if ( nit == null_node) { */
  /*   assign_succ(heap, nnew, null_node, 0); */
  /*   assign_ptr(heap, it, nnew); */
  /*   return; */
  /* } */

  //  prev_nit -----d-------> nit ---> null
  // to
  //  prev_nit -d-> nnew -0-> nit ---> null
  
  node_t prev_nit = prev(heap, nit);
  // nnew points to nit
  assign_succ(heap, nnew, nit, 0);

  // set the nprev that used to point to nit to point to nnew
  if (prev_nit != null_node) {
    assign_succ(heap, prev_nit, nnew, dist(heap, prev_nit));
    invalidate_prev(heap, nnew);
  } else {
    // we are adding at the beginning of the list so
    // replace all lists pointing to nit to point to the new list head nnew
    update_ptr(heap, nit, nnew);
  }
  invalidate_succ(heap, nit);
}

/* Iterator set - sets the last value returned by next */
void setI(abstract_heapt *heap,
	  ptr_t it,
	  data_t val)  {

  Assume (it < NPROG);
  Assert (is_iterator(heap, it), "INV_ERROR");
  
  node_t nx = deref(heap, it);
  
  // LSH FIXME: cannot get prev of null_node
  Assume (nx != null_node);

  node_t nprev = prev(heap, nx);
  Assert (nprev != null_node, "INV_ERROR");
  
  assign_data(heap, nprev, val);
}


/* Iterator remove - removes the last value returned by next */
void removeI(abstract_heapt *heap,
	     ptr_t it)  {
  Assume (it < NPROG);
  Assert (is_iterator(heap, it), "INV_ERROR");
  
  node_t nit = deref(heap, it);
  // FIXME: we cannot compute the prev of null currently 
  Assume(nit != null_node);
  // the node we will be removing
  node_t nrem = prev(heap, nit);

  // it cannot point to the beggining of the list
  // (no previous element to remove)
  Assert (nrem != null_node, "INV_ERROR");

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
	Assume(eval_pred(pi, data));
	assign_univ(heap, nrem, pi, bool_true);
      } else {
	assign_univ(heap, nrem, pi, bool_unknown);
      } 
      // false existentials are maintained
      /* if (get_exists(heap, nrem, pi) == bool_false) { */
      /* 	Assume(!eval_pred(pi, data)); */
      /* 	assign_exists(heap, nrem, pi, bool_false); */
      /* } else { */
      /* 	assign_exists(heap, nrem, pi, bool_unknown); */
      /* } */
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
    /* bool_t new_exists =  or (get_exists(heap, nprev, pi), */
    /* 			     get_exists(heap, nrem, pi)); */
    assign_univ(heap, nprev, pi, new_univ);
    //assign_exists(heap, nprev, pi, new_exists);
    assign_succ(heap, nprev, nit, s_add(dist(heap, nprev), dist(heap, nrem)) - 1);
    clear_node(heap, nrem);
  }
}

/* Iterator next */
word_t next(abstract_heapt *heap,
	    ptr_t it) {
  Assert (is_iterator(heap, it), "INV_ERROR");
  
  Assume(it < NPROG);

  node_t nit = deref(heap, it);
  Assert (nit != null_node, "INV_ERROR");

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
  Assert (is_iterator(heap, it), "INV_ERROR");
  return !is_null(heap, it);
}


/* Return the next index pointed to by iterator */
index_t nextIndex(abstract_heapt *heap,
		  ptr_t x) {
  Assert(0, "INV_ERROR");
  return -1;
}

