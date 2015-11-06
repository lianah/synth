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
  
  [ptrs, iterators, succs, prevs, datas, dists, univs, exists, nnodes] = [eval(g) for g in m]

  for u in univs:
    assert (len(u) == 1)

  univs = [u.pop() for u in univs]
  exists = [e.pop() for e in exists]

  assert (len(succs) == len(dists) and \
          len(dists) == len(univs) and \
          len(univs) == len(exists) and \
          len(datas) == len(exists))
  
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
      print r'heap->universal[%d][0] = %d;' % (i, univs[i])

  print "// set existantials"
  for i in range(len(exists)):
      print r'heap->existential[%d][0] = %d;' % (i, exists[i])

  print "heap->nnodes =", nnodes, ";"

regex = 'h={[^.]*\.ptr={([\d, ]*)},[^.]*\.is_iterator={([FALSETRU, ]*)},[^.]*\.succ={([\d, ]*)},[^.]*\.prev={([\d, ]*)},[^.]*\.data={([\d, ]*)},[^.]*\.dist={([\d, ]*)},[^.]*\.universal={([\d,{} ]*)},[^.]*\.existential={([\d,{} ]*)},[^.]*\.nnodes=(\d+)'

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

