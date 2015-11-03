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

def bool_t(x):
  assert (x < 3)
  if x == 2:
    return "?"
  return str(x)
  
def processHeap(m,prefix):
  print r'subgraph cluster_h%d {' % (prefix)
  print r'label=h%d' % (prefix)

  [ptrs, succs, dists, univs, exists, nnodes] = [eval(g) for g in m]

  for u in univs:
    assert (len(u) == 1)

  univs = [bool_t(u.pop()) for u in univs]
  exists = [bool_t(e.pop()) for e in exists]
  
  for n in xrange(nnodes):
    print r'node%d%d [label="%s"];' % (prefix, n, nodeptrs(n, ptrs))


  for n in xrange(nnodes):
    s = succs[n]
    d = dists[n]
    u = univs[n]
    e = exists[n]
    print r'node%d%d -> node%d%d [label="%d U=%s E=%s"];' % (i,n, i, s, d, u, e)

  print "}"


regex = 'ptr = {([\d, ]*)}, succ = {([\d, ]*)}, dist = {([\d, ]*)}, universal = {([\d,{} ]*)}, existential = {([\d,{} ]*)}, nnodes = (\d+)'
# regex = 'ptr = {([\d, ]*)}, succ={([\d, ]*)}, dist = {([\d, ]*)}, universal = {([\d,{} ]*)}, existential = {([\d,{} ]*)}, nnodes = (\d+)'


cex = sys.stdin.read()

heaps = re.findall(regex, cex)

print "digraph {"

for i in range(0, len(heaps)):
  processHeap(heaps[i], i)

print "}"  
