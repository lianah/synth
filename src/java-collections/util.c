
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include "abstract_heap.h"

/*
 * Saturating addition.
 */
word_t s_add(word_t x, word_t y) {
  word_t ret = (x > INF - y) ? INF : x + y;

  Assume(ret != INF || x == INF || y == INF);

  return ret;
}

bool_t and(bool_t x, bool_t y) {
  // LSH TODO: clever bit-fiddling?
  if ( x == bool_unknown || y == bool_unknown) {
    return (x == bool_false || y == bool_false) ? bool_false : bool_unknown;
  }
  return x && y;
}

bool_t or(bool_t x, bool_t y) {
  // LSH TODO: clever bit-fiddling?
  if ( x == bool_unknown || y == bool_unknown) {
    return (x == bool_true || y == bool_true) ? bool_true : bool_unknown;
  }
  return x || y;
}

/*
 * Saturating subtraction.
 */
word_t s_sub(word_t x, word_t y) {
  if (x == INF) {
    return INF;
  } else if (y > x) {
    return 0;
  } else {
    return x - y;
  }
}


#define LINEWIDTH 6
char *ptrnames[] = {"NULL", "x", "y", "z", "w", "q"};

void print_ptr(word_t p) {
  if (p < sizeof(ptrnames)) {
    printf("%s", ptrnames[p]);
  } else {
    printf("p%d", p);
  }
}

void print_len(word_t l) {
  if (l == INF) {
    printf("INF");
  } else {
    printf("%d", l);
  }
}

void print_abstract_heap(abstract_heapt *heap) {

  printf("Heap contains %d nodes\n", heap->nnodes);

  printf("Successors:");

  node_t n, m;
  word_t len;

  for (n = 0; n < NABSNODES; n++) {
    if (n % LINEWIDTH == 0) {
      printf("\n");
    }

    m = heap->succ[n];
    len = heap->dist[n];

    printf("%d -", n); print_len(len); printf("-> %d    ", m);
  }

  printf("\nPointers:");

  ptr_t p;

  for (p = 0; p < NPROG; p++) {
    if (p % LINEWIDTH == 0) {
      printf("\n");
    }

    n = heap->ptr[p];

    print_ptr(p); printf(" == %d;  ", n);
  }

  printf("\n");
}

#ifndef __CPROVER

void dump_heap(abstract_heapt *heap,
	       const char* heap_name,
	       const char* pretty_args) {
  FILE *fp;
  fp = fopen("heap.txt", "w+");
  int i;
  fprintf(fp, "{ ptr = { %d", heap->ptr[0]);
  for (i = 1; i < NPROG; ++i) {
    fprintf(fp, ", %d", heap->ptr[i]);
  }

  fprintf(fp, "}, is_iterator = {%s", (heap->is_iterator[0] ? "true" : "false" ));

  for (i = 1; i < NPROG; ++i) {
    fprintf(fp, ", %s", (heap->is_iterator[i] ? "true" : "false" ));
  }
  
  fprintf(fp, "}, succ = {%d", heap->succ[0]);
  for (i = 1; i < NABSNODES; ++i) {
    fprintf(fp, ", %d", heap->succ[i]);
  }

  fprintf(fp, "}, prev = {%d", heap->prev[0]);
  for (i = 1; i < NABSNODES; ++i) {
    fprintf(fp, ", %d", heap->prev[i]);
  }

  fprintf(fp, "}, data = {%d", heap->data[0]);
  for (i = 1; i < NABSNODES; ++i) {
    fprintf(fp, ", %d", heap->data[i]);
  }

  fprintf(fp, "}, dist = {%d", heap->dist[0]);
  for (i = 1; i < NABSNODES; ++i) {
    fprintf(fp, ", %d", heap->dist[i]);
  }

  fprintf(fp, "}, universal = {{");
  int j;
  fprintf(fp, "%d", heap->universal[0][0]);
  for (j = 0; j < NPREDS; ++j) {
    fprintf(fp, ", %d", heap->universal[0][j]);
  }
  fprintf(fp, "}");
  for (i = 1; i < NABSNODES; ++i) {
    fprintf(fp, ", {%d", heap->universal[i][0]);
    for (j = 0; j < NPREDS; ++j) { 
      fprintf(fp, ", %d", (int)(heap->universal[i][j]));
    }
    fprintf(fp, "}");
  }

  fprintf(fp, "}, nnodes = %d, sorted = {%d", heap->nnodes, heap->sorted[0]);
    for (i = 1; i < NABSNODES; ++i) {
    fprintf(fp, ", %d", heap->sorted[i]);
  }
    

    fprintf(fp, "}, min = {%d", heap->min[0]);
    for (i = 1; i < NABSNODES; ++i) {
    fprintf(fp, ", %d", heap->min[i]);
  }
    

    fprintf(fp, "}, max = {%d", heap->max[0]);
    for (i = 1; i < NABSNODES; ++i) {
    fprintf(fp, ", %d", heap->max[i]);
  }

  fprintf(fp, "}");
  
  // closing heap paren
  fprintf(fp, "}");
  fclose(fp);
  char command[400];
  strcpy(command, "cat heap.txt | ./pretty-gcc-heap.py ");
  strcat(command, pretty_args);
  strcat(command, "| dot -Tpng >");
  strcat(command, heap_name);
  strcat(command, ".png");
  printf("Running %s\n", command);
  
  system(command);
  
}

#endif

/* void print_facts(heap_factst *facts) { */
/*   ptr_t p, q; */
/*   word_t len; */

/*   printf("Shortest paths:\n"); */

/*   for (p = 0; p < NPROG; p++) { */
/*     for (q = 0; q < NPROG; q++) { */
/*       len = facts->dists[p][q]; */
/*       print_ptr(p); printf(" -"); print_len(len); printf("-> "); print_ptr(q); printf("   "); */
/*     } */

/*     printf("\n"); */
/*   } */
/* } */

/* void serialize_facts(heap_factst *facts, word_t buf[NARGS]) { */
/*   word_t i, j; */

/*   for (i = 0; i < NPROG; i++) { */
/*     for (j = 0; j < NPROG; j++) { */
/*       buf[i*NPROG + j] = facts->dists[i][j]; */
/*     } */
/*   } */

/*   for (i = NPROG*NPROG; i < NARGS; i++) { */
/*     buf[i] = 0; */
/*   } */
/* } */

/* void deserialize_heap(word_t buf[NARGS], abstract_heapt *heap) { */
/*   word_t i = 0; */
/*   word_t j; */

/*   for (j = 0; j < NABSNODES; j++) { */
/*     heap->succ[j] = buf[i++]; */
/*   } */

/*   for (j = 0; j < NABSNODES; j++) { */
/*     heap->dist[j] = buf[i++]; */
/*   } */

/*   for (j = 0; j < NPROG; j++) { */
/*     heap->ptr[j] = buf[i++]; */
/*   } */

/*   heap->nnodes = buf[i++]; */
/* } */
