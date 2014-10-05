#include "heapabstract.h"

#include <string.h>

static void copy_abstract(abstract_heapt *pre,
                          abstract_heapt *post) {
  memcpy(post, pre, sizeof(abstract_heapt));
}

/*
 * Dereference p -- which node does p point to?
 */
static node_t deref(abstract_heapt *heap,
                    ptr_t p) {
  // Ensure p is a real pointer.
  assert(p < NPROG);
  return heap->ptr[p];
}

/*
 * Next operator -- which node is in n's next pointer?
 */
static node_t next(abstract_heapt *heap,
                   node_t n) {
  // Ensure n is an allocated node.
  assert(n < heap->nnodes);
  return heap->succ[n];
}

/*
 * How far away is n's successor?
 */
static word_t dist(abstract_heapt *heap,
                   node_t n) {
  assert(n < heap->nnodes);
  return heap->dist[n];
}



/*
 * Replace node n with node m, i.e. every pointer that used to
 * point to n will now point to m.
 */
static void destructive_move_node(abstract_heapt *heap,
                                  node_t n,
                                  node_t m) {
  assert(n < heap->nnodes);
  assert(m < heap->nnodes);

  if (n == m) {
    // No need to do anything!;
    return;
  }

  ptr_t p;

  // First reassign the program variables...
  for (p = 0; p < NPROG; p++) {
    if (deref(heap, p) == n) {
      heap->ptr[p] = m;
    }
  }

  node_t x;
  // Now reassign the "next" pointers for each node.
  for (x = 0; x < heap->nnodes; x++) {
    if (next(heap, x) == n) {
      heap->succ[x] = m;
    }
  }
}

/*
 * Reclaim any nodes that are no longer reachable.
 */
static void destructive_gc(abstract_heapt *heap) {
  word_t is_reachable[NABSNODES];

  memset(is_reachable, 0, sizeof(is_reachable));

  // We're going to do a mark-and-sweep garbage collection.
  // First mark all of the program variables as reachable.
  ptr_t p;
  node_t n;

  for (p = 0; p < NPROG; p++) {
    n = deref(heap, p);

    is_reachable[n] = 1;
  }

  // Now do the transitive closure of the reachability relation.
  node_t i, j;

  assert(heap->nnodes <= NABSNODES);

  for (i = 0; i < heap->nnodes; i++) {
    for (j = 0; j < heap->nnodes; j++) {
      if (is_reachable[j]) {
        n = next(heap, j);
        is_reachable[n] = 1;
      }
    }
  }

  // Now copy all of the reachable nodes into the next generation.
  node_t reachable_nodes[NABSNODES];
  word_t nreachable = 0;

  for (n = 0; n < heap->nnodes; n++) {
    if (is_reachable[n]) {
      reachable_nodes[nreachable] = n;
      nreachable++;
    }
  }

  word_t ncopied = 0;
  word_t k;

  for (k = 0; k < nreachable; k++) {
    n = reachable_nodes[k];
    destructive_move_node(heap, n, ncopied);
    ncopied++;
  }

  heap->nnodes = ncopied;
}

/*
 * x = n;
 *
 * x is a pointer, n is a graph node.
 */
static void destructive_assign_ptr(abstract_heapt *heap,
                                   ptr_t x,
                                   node_t n) {
  assert(x < NPROG);
  assert(n < heap->nnodes);

  word_t px = heap->ptr[x];
  heap->ptr[x] = n;
}

/*
 * x.n = y;
 *
 * x and y are nodes.
 */
static void destructive_assign_next(abstract_heapt *heap,
                                    node_t x,
                                    node_t y,
                                    word_t dist) {
  assert(x < heap->nnodes);
  assert(y < heap->nnodes);

  node_t xn = next(heap, x);

  heap->succ[x] = y;
  heap->dist[x] = dist;
}

/*
 * x = y;
 *
 * x and y are pointers.
 */
void abstract_assign(abstract_heapt *pre,
                     abstract_heapt *post,
                     ptr_t x,
                     ptr_t y) {
  assert(x < NPROG);
  assert(y < NPROG);

  copy_abstract(pre, post);

  node_t py = deref(post, y);
  destructive_assign_ptr(post, x, py);

  destructive_gc(post);
}

/*
 * Allocate a new node.
 */

static node_t destructive_alloc(abstract_heapt *heap) {
  assert(heap->nnodes < NABSNODES);

  return heap->nnodes++;
}

/*
 * x = new();
 */
void abstract_new(abstract_heapt *pre,
                  abstract_heapt *post,
                  ptr_t x) {
  assert(x < NPROG);

  copy_abstract(pre, post);

  // Just allocate a new node and have x point to it.
  node_t n = destructive_alloc(post);
  destructive_assign_ptr(post, x, n);

  destructive_gc(post);
}

/*
 * x = y->n
 */
void abstract_lookup(abstract_heapt *pre,
                     abstract_heapt *post,
                     ptr_t x,
                     ptr_t y) {
  assert(x < NPROG);
  assert(y < NPROG);

  node_t py = deref(pre, y);
  node_t yn = next(pre, py);

  word_t y_yn_dist = dist(pre, py);

  __CPROVER_assume(py != null_node);

  assert(y_yn_dist > 0);

  // Two cases: 
  //
  // (1): y has a direct successor, i.e. y -1> z
  // (2): y's successor is some distance > 1 away, i.e. y -k-> z
  if (y_yn_dist == 1) {
    // Case 1:
    //
    // y's successor is one step away, so now x points to that
    // successor -- this is just a simple assign to the successor node.
    abstract_assign_node(x, yn, pre, post);
  } else {
    // Case 2:
    //
    // y's successor is more than one step away, so we need to introduce
    // an intermediate node n, which will become y's successor and which x
    // will point to, i.e.
    //
    // Pre state:
    //
    // y -k> z
    //
    // Post state:
    //
    // y -1> x -(k-1)> z
    copy_abstract(pre, post);

    // Now allocate a new node between y and yn.
    node_t n = destructive_alloc(post);
    word_t new_dist = s_sub(y_yn_dist, 1);
    destructive_assign_next(post, n, yn, new_dist);

    // Reassign y's next pointer to the newly allocated node.
    destructive_assign_next(post, py, n, 1);

    // And make x point to the new node.
    destructive_assign_ptr(post, x, n);

    destructive_gc(post);
  }
}

/*
 * x->n = y;
 */
void abstract_update(abstract_heapt *pre,
                     abstract_heapt *post,
                     ptr_t x,
                     ptr_t y) {
  assert(x < NPROG);
  assert(y < NPROG);

  copy_abstract(pre, post);

  node_t px = deref(post, x);
  node_t xn = next(post, x);

  node_t py = deref(post, y);

  destructive_assign_next(post, px, py, 1);
  destructive_gc(post);
}

/*
 * Check that the heap is well formed.
 */
int valid_abstract_heap(abstract_heapt *heap) {
  // NULL points to the null nodes.
  if (deref(heap, null_ptr) != null_node) {
    return 0;
  }

  // The null node doesn't point anywhere.
  if (next(heap, null_node) != null_node) {
    return 0;
  }

  if (dist(heap, null_node) != 0) {
    return 0;
  }

  // Each program variable points to a valid node.
  ptr_t p;

  for (p = 0; p < NPROG; p++) {
    if (deref(heap, p) >= heap->nnodes) {
      return 0;
    }
  }

  // Each node's next pointer points to a valid node.
  node_t n;

  for (n = 0; n < heap->nnodes; n++) {
    if (next(heap, n) >= heap->nnodes) {
      return 0;
    }
  }

  // Each node, except null, is > 0 away from its successor.
  for (n = 0; n < heap->nnodes; n++) {
    if (dist(heap, n) <= 0) {
      return 0;
    }
  }

  return 1;
}
