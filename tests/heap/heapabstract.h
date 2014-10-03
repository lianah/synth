#ifndef HEAPABSTRACT_H
#define HEAPABSTRACT_H

#include <stdio.h>
#include <assert.h>

#ifdef VERIF
 #define WIDTH 3
 typedef unsigned __CPROVER_bitvector[WIDTH] word_t;
 #define INF ((word_t) -1)
#else
 typedef unsigned int word_t;
 #define INF 0xffffffff
 #define __CPROVER_assume(x)
#endif

#ifndef NNODES
 #define NNODES 5
#endif

#ifndef NPROG
 #define NPROG NNODES
#endif

#define min(x, y) (x < y ? x : y)

typedef struct concrete_heap {
  word_t succ[NNODES];
  word_t ptr[NPROG];
} concrete_heapt;

typedef struct abstract_heap {
  word_t dist[NPROG][NPROG];
  word_t cut[NPROG][NPROG];
  word_t cut_cut[NPROG][NPROG];
  word_t stem[NPROG];
  word_t cycle[NPROG];
} abstract_heapt;

word_t nil = 0;

void print_concrete(concrete_heapt *heap);
void print_abstract(abstract_heapt *abstract);

void abstract(concrete_heapt *concrete,
              abstract_heapt *abstraction);

int is_valid_heap(concrete_heapt *heap);

int succ(concrete_heapt *heap, word_t x);

int heaps_isomorphic(concrete_heapt *heap1,
                     concrete_heapt *heap2);

int abstractions_equal(abstract_heapt *heap1,
                       abstract_heapt *heap2);

void concrete_assign(word_t x,
                     word_t y,
                     concrete_heapt *pre,
                     concrete_heapt *post);
void abstract_assign(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post);

void concrete_lookup(word_t x,
                     word_t y,
                     concrete_heapt *pre,
                     concrete_heapt *post);
void abstract_lookup(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post);

void concrete_update(word_t x,
                     word_t y,
                     concrete_heapt *pre,
                     concrete_heapt *post);
void abstract_update(word_t x,
                     word_t y,
                     abstract_heapt *pre,
                     abstract_heapt *post);

void concrete_new(word_t x,
                  concrete_heapt *pre,
                  concrete_heapt *post);
void abstract_new(word_t x,
                  abstract_heapt *pre,
                  abstract_heapt *post);

void copy_abstract(abstract_heapt *pre,
                   abstract_heapt *post);

int is_valid_abstract_heap(abstract_heapt *heap);
int path(abstract_heapt *heap,
         word_t a,
         word_t b);
int alias(abstract_heapt *heap,
          word_t a,
          word_t b);
int cut(abstract_heapt *heap,
        word_t a,
        word_t b);

word_t s_add(word_t x, word_t y);
word_t s_sub(word_t x, word_t y);

#endif // HEAPABSTRACT_H
