#!/usr/bin/python

import re
import sys


def processHeap(m):
  [ptrs, succs, dists, univs, exists, nnodes] = [eval(g) for g in m]

  for u in univs:
    assert (len(u) == 1)

  univs = [u.pop() for u in univs]
  exists = [e.pop() for e in exists]

  assert (len(succs) == len(dists) and \
          len(dists) == len(univs) and len(univs) == len(exists))
  
  print "// set pointers"
  for i in range(len(ptrs)):
      print r'heap->ptr[%d] = %d;' % (i, ptrs[i])

  print "// set successors"
  for i in range(len(succs)):
      print r'heap->succ[%d] = %d;' % (i, succs[i])
      
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

regex = 'h={[^.]*\.ptr={([\d, ]*)},[^.]*\.succ={([\d, ]*)},[^.]*\.dist={([\d, ]*)},[^.]*\.universal={([\d,{} ]*)},[^.]*\.existential={([\d,{} ]*)},[^.]*\.nnodes=(\d+)'

cex = sys.stdin.read()

heaps = re.findall(regex, cex)
assert (len(heaps) == 2)

print "#include \"abstract_heap.h\"\n"

print "void init_counterexample(abstract_heapt *heap) {"
processHeap(heaps[0])
print "}\n"

print "void inductive_counterexample(abstract_heapt *heap) {"
processHeap(heaps[1])
print "}"

