#ifndef CONCRETE_HEAP_H
#define CONCRETE_HEAP_H

#include "abstract_heap.h"

#ifndef NNODES
 #define NNODES 5
#endif

typedef struct concrete_heap { 
  node_t succ[NNODES];
  node_t ptr[NPROG];
} concrete_heapt;


void print_concrete(concrete_heapt *heap);
void print_abstract(abstract_heapt *abstract);
void print_facts(heap_factst *facts);

void abstract(concrete_heapt *concrete,
              abstract_heapt *abstraction);

int is_valid_heap(concrete_heapt *heap);

int succ(concrete_heapt *heap, word_t x);

int heaps_isomorphic(concrete_heapt *heap1,
                     concrete_heapt *heap2);

void consequences(abstract_heapt *heap,
                  heap_factst *facts);

void concrete_assign(concrete_heapt *pre,
                     concrete_heapt *post,
                     ptr_t x,
                     ptr_t y);
void concrete_lookup(concrete_heapt *pre,
                     concrete_heapt *post,
                     ptr_t x,
                     ptr_t y);
void concrete_update(concrete_heapt *pre,
                     concrete_heapt *post,
                     ptr_t x,
                     ptr_t y);
void concrete_new(concrete_heapt *pre,
                  concrete_heapt *post,
                  word_t x);

int valid_abstract_heap(abstract_heapt *heap);
int is_minimal(abstract_heapt *heap);


#endif // CONCRETE_HEAP_H
