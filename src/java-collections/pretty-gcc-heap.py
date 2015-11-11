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


def preds_str(us):
  string = ""
  for u in us:
    if u == 2:
      string += "? "
    elif u == 1:
      string += "T "
    elif u == 0:
      string += "F "
    else:
      assert(false)
  return string
  
  
def processHeap(m,prefix):
  print r'subgraph cluster_h%d {' % (prefix)
  print r'label=h%d' % (prefix)

  m = list(m)
  m[1] = m[1].replace("false", "0")
  m[1] = m[1].replace("true", "1")
  m[6] = m[6].replace("{","[")
  m[6] = m[6].replace("}","]")

  
  [ptrs, iterators, succs, prevs, datas, dists, univs, nnodes, sorts, mins, maxs] = [eval(g) for g in m]


  univs = [preds_str(u) for u in univs]
  
  for n in xrange(nnodes):
    data = datas[n]
    print r'node%d%d [label="%s [%d]"];' % (prefix, n, nodeptrs(n, ptrs), data)


  for n in xrange(nnodes):
    s = succs[n]
    d = dists[n]
    u = univs[n]
    print r'node%d%d -> node%d%d [label="%d U=%s"];' % (i,n, i, s, d, u)

  print "}"


regex = 'h={[^.]*\.ptr={([\d, ]*)},[^.]*\.is_iterator={([FALSETRU, ]*)},[^.]*\.succ={([\d, ]*)},[^.]*\.prev={([\d, ]*)},[^.]*\.data={([\d, ]*)},[^.]*\.dist={([\d, ]*)},[^.]*\.universal={([\d,{} ]*)},[^.]*\.nnodes=(\d+),[^.]*\.sorted={([\d, ]*)},[^.]*\.min={([\d, ]*)},[^.]*\.max={([\d, ]*)}'

cex = sys.stdin.read()

heaps = re.findall(regex, cex)

print "digraph {"

for i in range(0, len(heaps)):
  processHeap(heaps[i], i)

print "}"  
