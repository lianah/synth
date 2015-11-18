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


word_t nondet_word_t() {
  word_t d;
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
word_t nondet_word_t();

#endif


/*
 * Dereference p -- which node does p point to?
 */
node_t deref(const abstract_heapt *heap,
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
		   node_t nlist,
                   node_t n) {
  // Ensure n is an allocated node.
  Assume(n < NABSNODES);
  if (nlist == n)
    return null_node;
  
  //Assert(n != null_node, "INV_ERROR: prev");
  word_t i;
  for (i = 0; i < NABSNODES; ++i) {
    if (succ(heap, nlist) == n)
      return nlist;
    nlist = succ(heap, nlist);
  }
  assert(0);
  return null_node;
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
  _Bool res = predicates[pi](val);

  return res;
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
			bool_t sorted_val) {
  Assume(nx < NABSNODES);
  heap->sorted[nx] = sorted_val;
}

static void assign_min_max(abstract_heapt *heap,
			node_t nx,
			data_t min_val,
			data_t max_val) {
  Assume(nx < NABSNODES);
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


/* static void assign_prev(abstract_heapt *heap, */
/* 			node_t x, */
/* 			node_t y) { */
/*   Assume(x < NABSNODES); */
/*   Assume(y < NABSNODES); */
  
/*   heap->prev[x] = y; */
/* } */


static void assign_succ(abstract_heapt *heap,
			node_t x,
			node_t y,
			word_t dist) {
  Assume(x < NABSNODES);
  Assume(y < NABSNODES);
  
  heap->succ[x] = y;
  //heap->prev[y] = x;
  
  heap->dist[x] = dist;
  
  predicate_index_t pi = 0;
  if (dist == 0) {
    for (pi = 0; pi < NPREDS; ++pi) {
      assign_univ(heap, x, pi, bool_true);
    }
    assign_sorted(heap, x, bool_true);
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
  //assign_prev(heap, nx, null_node);
  assign_ptr(heap, x, nx);
}

/*
  Subdivides an edge (a, c), creating two edges with appropriate predicate labels.
  The subdivision is done by creating, and returning, a new node b between a and c:

     a ---> b ---> c

  such that path_len(a, b) = pos, and path_len(b, c) = path_len(a, c) - pos.

  If pos=0, no subdivision is done and we just return a.

  If pos = path_len(a, c), no subdivision is done and we just return c.
 */
node_t subdivide(abstract_heapt *heap,
		 node_t nx,
		 word_t pos) {


  Assert (nx < NABSNODES, "INV_ERROR");

  node_t succ_nx = succ(heap, nx);
  word_t nx_dist = dist(heap, nx);

  // no need to create a new node just return nx
  if (pos == 0) {
    return nx;
  } else if (pos == s_add(nx_dist, 1)) {
    return succ_nx;
  }

  Assert (pos <= nx_dist, "INV_ERROR: edge too short cannot subdivide.");
  
  node_t nnew = alloc(heap);
  //assign_prev(heap, nnew, null_node);
  word_t dist1 = s_sub(pos, 1);
  word_t dist2 = s_sub(nx_dist, pos);
  
  predicate_index_t pi;
  for (pi = 0; pi < NPREDS; ++pi) {
    bool_t pred = get_univ(heap, nx, pi) == bool_true;
    // Assume the predicates for the values stored at nnew
    // Only true universals are still true on the data
    if (pred == bool_true) {
#ifdef __CPROVER      
      Assume(eval_pred(pi, data(heap, nnew)));
#endif      
      assign_univ(heap, nnew, pi, bool_true);
      // for nx the univ stays true
    } else {
      // both segments are unknown if the predicate was false or unknown
      assign_univ(heap, nnew, pi, bool_unknown);
      assign_univ(heap, nx, pi, bool_unknown);
    }
  }

  // FOR SORTED:
  // Assume min <= val <= max
  Assume(get_min(heap, nx) <= get_min(heap, nnew));
  Assume(get_min(heap, nnew) <= data(heap, nnew));
  Assume(data(heap, nnew) <= get_max(heap, nnew));
  Assume(get_max(heap, nnew) <= get_max(heap, nx));

  if(dist(heap, nnew) == 0 && !is_null(heap, nnew)) {
    Assume(get_min(heap, nnew) == data(heap, nnew));
    Assume(get_max(heap, nnew) == data(heap, nnew));
  }
  // additional constraints if the edge is sorted
  if(get_sorted(heap, nx) == bool_true) {
    Assume(data(heap, nx) <= data(heap, nnew));
    Assume(data(heap, nnew) <= get_min(heap, nnew));
  }
  assign_sorted(heap, nnew, get_sorted(heap, nx));
  assign_sorted(heap, nx, bool_true);


  // Reassign nnew's succ pointer to nx's successor succ_nx
  assign_succ(heap, nnew, succ_nx, dist2);
  // Reassign nx's succ pointer to the newly allocated node.
  assign_succ(heap, nx, nnew, dist1);

  
  return nnew;
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
			    node_t nlist,
			    node_t nx) {
  //Assert (nx != null_node, "INV_ERROR");

  word_t i;
  for (i = 1; i < NABSNODES; ++i) {
    // we want to exclude the first pointer
    if (succ(heap, nlist) == nx) {
      return;
    }
    invalidate(heap, nlist);
    nlist = succ(heap, nlist);
  }
  assert(0);
}


/* Returns the last node x such that path_len(node, x) <= index */

extern node_t get_segment(abstract_heapt* heap,
			 node_t node,
			 index_t index) {
  word_t i, len = 0;

  for (i = 0; i < NABSNODES; ++i) {
    len = s_add(len, dist(heap, node));
    len = s_add(len, 1);

    if (len > index) {
      return node;
    }

    node = succ(heap, node);
  }

  return node;
}

/* Remove the node nrem and updates head of list if necessary */
extern void remove_helper(abstract_heapt* heap,
			  node_t nlist,
			  node_t nrem) {
  // the node before the one we are removing
  node_t nprev = prev(heap, nlist, nrem);
  // the node after the one we are removing
  node_t nit = succ(heap, nrem);
  
  predicate_index_t pi;

  // We are deleting the head of the list
  if (nprev == null_node) {
    
    // There is an node right after nrem so just make this one the head
    if (dist(heap, nrem) == 0) {
      // clear the node to be removed
      clear_node(heap, nrem);
      // invalidate all iterators pointing to it and
      // update lists to point to the new head
      invalidate_and_update(heap, nrem, nit);
      return;
    }

    // There is no new node so create new head of the list 
    // update the predicates and assume constraints on the new value
    word_t data;
    for (pi = 0; pi < NPREDS; ++pi) {
      // true universals are maintained
      if (get_univ(heap, nrem, pi) == bool_true) {
#ifdef __CPROVER	
	Assume(eval_pred(pi, data));
#endif	
	assign_univ(heap, nrem, pi, bool_true);
      } else {
	assign_univ(heap, nrem, pi, bool_unknown);
      } 
    }
    assign_data(heap, nrem, data);
    assign_succ(heap, nrem, nit, dist(heap, nrem) - 1);
    invalidate(heap, nrem);
    // LSH: do we need to update any sorted info?
    return;
  }
  
  // We are deleting a node in the middle
  for (pi = 0; pi < NPREDS; ++pi) {
    bool_t new_univ = and (get_univ(heap, nprev, pi),
			   get_univ(heap, nrem, pi));

    assign_univ(heap, nprev, pi, new_univ);
    assign_succ(heap, nprev, nit, s_add(dist(heap, nprev), dist(heap, nrem)));
    clear_node(heap, nrem);
    // LSH: do we need to update any sorted info?
  }
}

/* Add a node storing val right before the nx node */
extern void add_helper(abstract_heapt* heap,
		       node_t nlist,
		       node_t nit,
		       data_t val) {

  // create new node and set data
  node_t nnew = alloc(heap);

  // make sure the prev for the new node is initialized
  // (in case it ends up head of the list)
  //assign_prev(heap, nnew, null_node);
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
  
  node_t prev_nit = prev(heap, nlist, nit);
  // nnew points to nit
  assign_succ(heap, nnew, nit, 0);

  // set the nprev that used to point to nit to point to nnew
  if (prev_nit != null_node) {
    assign_succ(heap, prev_nit, nnew, dist(heap, prev_nit));
    invalidate_prev(heap, nlist, nnew);
  } else {
    // we are adding at the beginning of the list so
    // replace all lists pointing to nit to point to the new list head nnew
    update_ptr(heap, nit, nnew);
  }
  invalidate_succ(heap, nit);
}

/*
 * Accumulate the values of pi over data and edges */
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

    bool_t node_res = eval_pred(pi, data(heap, nx));
    bool_t edge_res = get_univ(heap, nx, pi);

    res = and(res, node_res);
    res = and(res, edge_res);

    nx = succ(heap, nx);
  }
  return bool_unknown;
}


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
  for (i = 0; i < heap->nnodes; ++i) {
    assume_consistent_node(heap, i);
  }
}

_Bool is_minimal(const abstract_heapt *heap) {
  word_t is_named[NABSNODES];
  memset(is_named, 0, sizeof(is_named));

  // Count the reachable nodes and find the indegrees of each node in the
  // reachable subheap.
  word_t is_reachable[NABSNODES];
  word_t indegree[NABSNODES];
  word_t nreachable = 0;

  memset(is_reachable, 0, sizeof(is_reachable));
  memset(indegree, 0, sizeof(indegree));

  ptr_t p;
  node_t n, m;
  word_t i;
  word_t last_reachable = 0;

  predicate_index_t pi; 
  
  for (p = 0; p < NPROG; p++) {
    Assume(heap->ptr[p] < heap->nnodes);
    
    n = deref(heap, p);
    is_named[n] = 1;

    if (n >= heap->nnodes) {
      return 0;
    }

    for (i = 0; i < NABSNODES-1; i++) {
      if (!is_reachable[n]) {
        if (n >= heap->nnodes) {
          return 0;
        }

        if (dist(heap, n) >= INF) {
          return 0;
        }

        if (n != null_node && dist(heap, n) <= 0) {
          return 0;
        }

        if (n < last_reachable) {
          // The heap is not topologically ordered.
          return 0;
        }

        last_reachable = n;

        is_reachable[n] = 1;
        nreachable++;
	
	// Check that the sorted and predicates are not unknown
	for (pi = 0; pi < NPREDS; ++pi) {
	  bool_t u = get_univ(heap, n, pi);
	  bool_t s = get_sorted(heap, n);
	  data_t mi = get_min(heap, n);
	  data_t ma = get_max(heap, n);

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

	  // enforce min = max = data for edges of length 0 (corresponding to segments of length 1)
	  if (dist(heap, n) == 0 && n != null_node && 
	      (mi != data(heap, n) || mi != ma)) {
	    return 0;
	  }

	  // enforce min <= max for all edges
	  if (mi > ma) {
	    return 0;
	  }
	}
	
        n = succ(heap, n);


        indegree[n]++;
      }
    }
  }

  // Check there are no unnamed, reachable nodes with indegree <= 1.
  for (n = 0; n < NABSNODES; n++) {
    if (!is_named[n] && is_reachable[n] && indegree[n] <= 1) {
      return 0;
    }
  }

  // If we're a fully reduced graph, we don't have any unreachable nodes.
  if (heap->nnodes != nreachable) {
    return 0;
  }

  if (nreachable > NABSNODES) {
    return 0;
  }

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


word_t node_path_len(const abstract_heapt *heap,
		     node_t n,
		     node_t yn) {
  word_t curr_dist = 0;
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
  
  //Assert (0, "INV_ERROR");
  return INF;
}

word_t path_len(const abstract_heapt *heap,
                ptr_t x,
                ptr_t y) {
  node_t n = deref(heap, x);
  node_t yn = deref(heap, y);

  return node_path_len(heap, n, yn);
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
  //Assert (0, "INV_ERROR");
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

_Bool forall_assume(const abstract_heapt *heap,
		    ptr_t x,
		    ptr_t y,
		    predicate_index_t pi) {

  /* Assume(is_path(heap, x, y)); */
  /* node_t nx = deref(heap, x); */
  /* node_t ny = deref(heap, y); */
  /* return path_forall(heap, nx, ny, pi) == bool_true; */

  return forall(heap, x, y, pi) == bool_true;
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

  return path_forall(heap, nx, ny, prop);

  /* // LSH: still having problems with copy-safe and reverse-safe? */
  
  /* _Bool data_prop = 1; */

  /* bool_t pred_vals[NPREDS]; */

  /* predicate_index_t pi; */
  /* for (pi = 0; pi < NPREDS; ++pi) { */
  /*   pred_vals[pi] = bool_true; */
  /* } */
  
  /* word_t i; */
  /* for (i = 0; i < NABSNODES; ++i) { */
  /*   if (nx == ny) { */
  /*     // universally quantify over val */
  /*     data_t val = nondet_data_t(); */
  /*     //val = 8; */
  /*     _Bool prop_true = 1; */
  /*     _Bool prop_false = 0; */
  /*     _Bool val_prop = eval_pred(prop, val); */
      
  /*     for (pi = 0; pi < NPREDS; ++pi) { */
  /* 	if (pred_vals[pi] == bool_true) { */
  /* 	  // if predicate holds add to positive predicates */
  /* 	  // AND Pi(val) */
  /* 	  prop_true = prop_true && eval_pred(pi, val); */
  /* 	} else if (pred_vals[pi] == bool_false) { */
  /* 	  // if predicate is false check if it entails negation of property */
  /* 	  // OR (~Pi(val) => Prop(val)) */
  /* 	  prop_false = prop_false || eval_pred(pi, val) || ! val_prop; */
  /* 	} */
  /*     } */

  /*     // LSH FIXME: with this condition if data_prop = false, then it will return true */
  /*     // which is not correct :( */
      
  /*     // The true predicates entail the property and the property holds on the data */
  /*     if ((!prop_true || val_prop) && data_prop) { */
  /* 	return bool_true; */
  /*     } */
      
  /*     // The true predicates entail the negation of the property or */
  /*     // the property fails on the data or */
  /*     // one of the negative predicates entails the negation of the property */
  /*     if (!data_prop || (!prop_true || !val_prop) || prop_false) { */
  /* 	return  bool_false; */
  /*     } */
  /*     return bool_unknown; */
  /*   } */
    
  /*   // evaluate the property no all data nodes */
  /*   data_prop = data_prop && eval_pred(prop, data(heap, nx)); */
  /*   // collect valuation of the edge predicate */
  /*   for (pi = 0; pi < NPREDS; ++pi) { */
  /*     pred_vals[pi] = and(pred_vals[pi], get_univ(heap, nx, pi)); */
  /*   } */
  /*   nx = succ(heap, nx); */
  /* } */
}


/*
  Is the segment from x to y sorted?
*/

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

  data_t old_max = data(heap, nx);
  bool_t res = bool_true;
  word_t i;

  for (i = 0; i < NABSNODES; ++i) {
    if (nx == ny) {
      return res;
    }

    res = and(res, old_max <= data(heap, nx));
    old_max = data(heap, nx);
    res = and(res, get_sorted(heap, nx));
    // if len > 0 then we must also consider the values of the abstracted segment
    if(dist(heap, nx) > 0) {
      res = and(res, old_max <= get_min(heap, nx));
      old_max = get_max(heap, nx);
    }

    nx = succ(heap, nx);
  }

  // LSH FIXME: paper actually checks entailment
  return bool_unknown;
}

/*
  What is the minimum value on the segment from x to y?
*/

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
}

/*
  What is the maximum value on the segment from x to y?
*/

data_t max(const abstract_heapt *heap,
	      ptr_t x,
	      ptr_t y) {

  Assume(is_path(heap, x, y));
    
  node_t nx = deref(heap, x);
  node_t ny = deref(heap, y);
 
  Assert(nx != ny, "MAX_FOR_EMPTY_SEG_ERR");

  word_t i;
  data_t curr_max = data(heap, nx);

  for (i = 0; i < NABSNODES; ++i) {
    if (nx == ny) {
      return curr_max;
    }

    if (data(heap, nx) > curr_max)
      curr_max = data(heap, nx);
    // if len > 0 then we must also consider the values of the abstracted segment
    if(dist(heap, nx) > 0) {
      if (get_max(heap, nx) > curr_max) {
	curr_max = get_max(heap, nx);
      }
    }

    nx = succ(heap, nx);
  }

  // LSH FIXME: paper actually checks entailment
  return bool_unknown;
}

node_t succP(abstract_heapt *heap,
    node_t node,
    index_t i) {
  Assert (i >= 0, "INV_ERROR: index must be positive");

  // get the node right before the segment on which i falls
  // or the node on which i falls if the node already exists
  node_t seg_node = get_segment(heap, node, i);
  word_t len = node_path_len(heap, node, seg_node);

  // subdivide this segment if necessary to create new node
  if (len == i) {
    return seg_node;
  } else if (len < i) {
    return subdivide(heap, seg_node, s_sub(i, len));
  } else {

    Assert (0, "INV_ERROR: wtf");
  }
}

/*************************
 *
 *  Abstract accessors
 * 
 ************************/

/* Positional get */
data_t getP(abstract_heapt *heap,
	    ptr_t list,
	    index_t i) {
  Assert (!is_iterator(heap, list), "INV_ERROR");
  Assert (i >= 0 && i <= path_len(heap, list, null_ptr), "INV_ERROR");
  node_t node = deref(heap, list);
  node_t pos_i = succP(heap, node, i);
  return data(heap, pos_i);
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

  node_t node = deref(heap, list);
  node_t to_set = succP(heap, node, i);
  Assert (to_set != null_node, "INV_ERROR: cannot set null node");
  assign_data(heap, to_set, val);
}


/* Positional add */
void addP(abstract_heapt *heap,
	  ptr_t list,
	  index_t i,
	  data_t val) {
  Assert(!is_iterator(heap, list), "INV_ERROR");
  
  node_t node = deref(heap, list);

  node_t add_before = succP(heap, node, i);

  add_helper(heap, node, add_before, val);
}

/* Positional remove */
void removeP(abstract_heapt *heap,
	     ptr_t list,
	     index_t i)  {
  Assert(!is_iterator(heap, list), "INV_ERROR");
  
  node_t node = deref(heap, list);
  node_t to_remove = succP(heap, node, i);

  remove_helper(heap, node, to_remove);
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

void listIterator(abstract_heapt* heap,
		  ptr_t it,
		  ptr_t list,
		  index_t i) {
  Assert (is_iterator(heap, it) &&
	  !is_iterator(heap, list), "INV_ERROR");

  node_t node = deref(heap, list);
  node_t nlist = succP(heap, node, i);
  assign_ptr(heap, it, nlist);
}


/* Iterator add - add val before the iterator it */
void addI(abstract_heapt *heap,
	  ptr_t list,
	  ptr_t it,
	  data_t val) {

  Assert (is_iterator(heap, it), "INV_ERROR");

  // LSH FIXME: this case not supported yet so use assume
  Assume (!is_null(heap, it));
  node_t nlist = deref(heap, list);
  node_t nit = deref(heap, it);
  add_helper(heap, nlist, nit, val);
}

/* Iterator set - sets the last value returned by next */
void setI(abstract_heapt *heap,
	  ptr_t list,
	  ptr_t it,
	  data_t val)  {

  Assume (it < NPROG);
  Assert (is_iterator(heap, it), "INV_ERROR");
  
  node_t nx = deref(heap, it);
  node_t nlist = deref(heap, list);
  // LSH FIXME: cannot get prev of null_node
  Assume (nx != null_node);

  node_t nprev = prev(heap, nlist, nx);
  Assert (nprev != null_node, "INV_ERROR");
  
  assign_data(heap, nprev, val);
}


/* Iterator remove - removes the last value returned by next */
void removeI(abstract_heapt *heap,
	     ptr_t list,
	     ptr_t it)  {
  Assume (it < NPROG);
  Assert (is_iterator(heap, it), "INV_ERROR");
  
  node_t nit = deref(heap, it);
  node_t nlist = deref(heap, list);
  // FIXME: we cannot compute the prev of null currently 
  Assume(nit != null_node);

  // We want to remove the node before nit
  node_t nprev = prev(heap, nlist, nit);
  
  // it could not have been the head of the list (no next)
  Assert (nprev != null_node, "INV_ERROR");

  // node to be removed
  node_t nrem; 
  if (dist(heap, nprev) == 0) {
    // we are removing nprev since is the one right before nit
    nrem = nprev;
  } else {
    // we need to subdivide the incoming edge as follows:
    // nprev ---------d-----------------> nit
    // nprev ------(d-1)-------nrem--0--> nit
    nrem = subdivide(heap, nprev, s_sub(dist(heap, nprev), 1)); 
  }

  remove_helper(heap, nlist, nrem);
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
  node_t succ_nit = dist(heap, nit) == 0? succ(heap, nit) :
                    subdivide(heap, nit, 1);
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

