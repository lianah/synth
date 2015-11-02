#include "abstract_heap.h"


  /* h={ .ptr={ 0, 2, 1 }, .succ={ 0, 0, 0, 0 }, .dist={ 0, 4, 4, 0 },
    .universal={ { 2 }, { 0 }, { 0 }, { 0 } }, .existential={ { 2 }, { 0 }, { 0 }, { 0 } },
    .nnodes=3 } ({ { 00000, 00010, 00001 }, { 00000, 00000, 00000, 00000 }, { 00000, 00100, 00100, 00000 }, { { 10 }, { 00 }, { 00 }, { 00 } }, { { 10 }, { 00 }, { 00 }, { 00 } }, 00011 })

  */
void init_counterexample(abstract_heapt *heap) {
  // set pointers
  heap->ptr[0] = 0;
  heap->ptr[1] = 2;
  heap->ptr[2] = 1;
  // set successors
  heap->succ[0] = 0;
  heap->succ[1] = 0;
  heap->succ[2] = 0;
  heap->succ[3] = 0;

  // set distances;
  heap->dist[0] = 0;
  heap->dist[1] = 4;
  heap->dist[2] = 4;
  heap->dist[3] = 0;

  // set universals
  heap->universal[0][0] = bool_unknown;
  heap->universal[1][0] = bool_false;
  heap->universal[2][0] = bool_false;
  heap->universal[3][0] = bool_false;

  // set existentials
  heap->existential[0][0] = bool_unknown;
  heap->existential[1][0] = bool_false;
  heap->existential[2][0] = bool_false;
  heap->existential[3][0] = bool_false;

  // set num nodes allocated

  heap->nnodes = 3;
}
/*

State 439 file ./shakira.c line 24 function main thread 0
----------------------------------------------------
  h={ .ptr={ 0, 1, 1 }, .succ={ 0, 0, 0, 0 }, .dist={ 0, 17, 1, 1 },
    .universal={ { 2 }, { 0 }, { 0 }, { 0 } }, .existential={ { 2 }, { 0 }, { 0 }, { 0 } },
    .nnodes=2 } ({ { 00000, 00001, 00001 }, { 00000, 00000, 00000, 00000 }, { 00000, 10001, 00001, 00001 }, { { 10 }, { 00 }, { 00 }, { 00 } }, { { 10 }, { 00 }, { 00 }, { 00 } }, 00010 })
*/
void inductive_counterexample(abstract_heapt *heap) {
  // set pointers
  heap->ptr[0] = 0;
  heap->ptr[1] = 1;
  heap->ptr[2] = 1;
  
  // set successors
  heap->succ[0] = 0;
  heap->succ[1] = 0;
  heap->succ[2] = 0;
  heap->succ[3] = 0;

  // set distances;
  heap->dist[0] = 0;
  heap->dist[1] = 17;
  heap->dist[2] = 1;
  heap->dist[3] = 1;

  // set universals
  heap->universal[0][0] = bool_unknown;
  heap->universal[1][0] = bool_false;
  heap->universal[2][0] = bool_false;
  heap->universal[3][0] = bool_false;

  // set existentials
  heap->existential[0][0] = bool_unknown;
  heap->existential[1][0] = bool_false;
  heap->existential[2][0] = bool_false;
  heap->existential[3][0] = bool_false;

  // set num nodes allocated
  heap->nnodes = 2;
}
