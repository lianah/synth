#!/usr/bin/python

import re
import sys


def nodeptrs(n, ptrs):
  return ', '.join([ptrname(p) for p in xrange(len(ptrs)) if ptrs[p] == n])

def ptrname(p):
  if p == 0:
    return "null"
  elif p < len(sys.argv):
    return sys.argv[p]
  else:
    return "ptr_%d" % p

  
def processHeap(m,prefix):
  print r'subgraph cluster_h%d {' % (prefix)
  print r'label=h%d' % (prefix)
  [succs, dists, ptrs, nnodes] = [eval(g) for g in m]

  for n in xrange(nnodes):
    print r'node%d%d [label="%s"];' % (prefix, n, nodeptrs(n, ptrs))


  for n in xrange(nnodes):
    s = succs[n]
    d = dists[n]
    print r'node%d%d -> node%d%d [label="%d"];' % (i,n, i, s, d)

  print "}"



regex = 'h={[^.]*\.succ={([\d, ]*)},[^.]*\.dist={([\d, ]*)},[^.]*\.ptr={([\d, ]*)},[^.]*\.nnodes=(\d+)'
# r = re.compile(r'h={[^.]*\.succ={([\d, ]*)},[^.]*\.dist={([\d, ]*)},[^.]*\.ptr={([\d, ]*)},[^.]*\.nnodes=(\d+)', flags=re.DOTALL)

cex = sys.stdin.read()

heaps = re.findall(regex, cex)


print "digraph {"

for i in range(0, len(heaps)):
  processHeap(heaps[i], i)

print "}"  
