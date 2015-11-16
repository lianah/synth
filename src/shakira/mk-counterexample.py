#!/usr/bin/python

import re
import sys

def boolean(i):
  if (i == "FALSE"):
    return 0;
  if (i == "TRUE"):
    return 1;
    
  assert(False);

def processHeap(m):
  m = list(m)
  m[1] = m[1].replace("FALSE", "0")
  m[1] = m[1].replace("TRUE", "1")
  m[6] = m[6].replace("{","[")
  m[6] = m[6].replace("}","]")

  [ptrs, iterators, succs, prevs, datas, dists, univs, nnodes, sorts, mins, maxs] = [eval(g) for g in m]


  assert (len(succs) == len(dists) and \
          len(dists) == len(univs) and \
          len(univs) == len(datas) and \
          len(mins) == len(maxs) and \
          len(maxs) == len(sorts) and \
          len(sorts) == len(univs))
  
  print "// set pointers"
  for i in range(len(ptrs)):
      print r'heap->ptr[%d] = %d;' % (i, ptrs[i])

  print "// set iterators"
  for i in range(len(iterators)):
      print r'heap->is_iterator[%d] = %d;' % (i, iterators[i])
      
      
  print "// set successors"
  for i in range(len(succs)):
      print r'heap->succ[%d] = %d;' % (i, succs[i])

  print "// set predecessors"
  for i in range(len(prevs)):
      print r'heap->prev[%d] = %d;' % (i, prevs[i])
      
  print "// set data"
  for i in range(len(datas)):
      print r'heap->data[%d] = %d;' % (i, datas[i])
      
      
  print "// set distances"
  for i in range(len(dists)):
      print r'heap->dist[%d] = %d;' % (i, dists[i])

  print "// set universals"
  for i in range(len(univs)):
    u = univs[i]
    for j in range(len(u)):
      print r'heap->universal[%d][%d] = %d;' % (i, j, u[j])

  print "// set sorted"
  for i in range(len(sorts)):
      print r'heap->sorted[%d] = %d;' % (i, sorts[i])

  print "// set min"
  for i in range(len(mins)):
      print r'heap->min[%d] = %d;' % (i, mins[i])

  print "// set max"
  for i in range(len(sorts)):
      print r'heap->max[%d] = %d;' % (i, maxs[i])
      
      
  # print "// set existantials"
  # for i in range(len(exists)):
  #     print r'heap->existential[%d][0] = %d;' % (i, exists[i])

  print "heap->nnodes =", nnodes, ";"

regex = 'h={[^.]*\.ptr={([\d, ]*)},[^.]*\.is_iterator={([FALSETRU, ]*)},[^.]*\.succ={([\d, ]*)},[^.]*\.prev={([\d, ]*)},[^.]*\.data={([\d, ]*)},[^.]*\.dist={([\d, ]*)},[^.]*\.universal={([\d,{} ]*)},[^.]*\.nnodes=(\d+),[^.]*\.sorted={([\d, ]*)},[^.]*\.min={([\d, ]*)},[^.]*\.max={([\d, ]*)}'

cex = sys.stdin.read()

heaps = re.findall(regex, cex)

assert (len(heaps) == 1 or len(heaps) == 2)

# It could be that the base case failed and we only have one counterexample
# heap so we just duplicate it

if(len(heaps) == 1):
  heaps.append(heaps[0])

print "#include \"abstract_heap.h\"\n"

print "void init_counterexample(abstract_heapt *heap) {"
processHeap(heaps[0])
print "}\n"

print "void inductive_counterexample(abstract_heapt *heap) {"
processHeap(heaps[1])
print "}"

