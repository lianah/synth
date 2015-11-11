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
  #assert (x < 3)
  if x >= 2:
    return "?"
  return str(x)

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
      string +="* "
  return string
      
  
def processHeap(m,prefix):
  print r'subgraph cluster_h%d {' % (prefix)
  print r'label=h%d' % (prefix)

  m = list(m)
  m[1] = m[1].replace("FALSE", "0")
  m[1] = m[1].replace("TRUE", "1")
  m[6] = m[6].replace("{","[")
  m[6] = m[6].replace("}","]")

  [ptrs, iterators, succs, prevs, datas, dists, univs, nnodes, sort, mins, maxs] = [eval(g) for g in m]

  for i in range(nnodes):
    for u in univs[i]:
      assert (u <= 2)

  # print "pointers ", ptrs
  # print "iterators ", iterators

  univs = [preds_str(u) for u in univs]

  # print univs
  # exists = [bool_t(e.pop()) for e in exists]
  
  for n in xrange(nnodes):
    d = datas[n]
    print r'node%d%d [label="%s [%d]"];' % (prefix, n, nodeptrs(n, ptrs), d)


  for n in xrange(nnodes):
    s = succs[n]
    d = dists[n]
    u = univs[n]
    # e = exists[n]
    p = prevs[n]
    so = sort[n]
    mi = mins[n]
    ma = maxs[n]
    
    print r'node%d%d -> node%d%d [label="%d %s %d %d %d"];' % (prefix,n, prefix, s, d, u, so, mi, ma)

    #print r'node%d%d -> node%d%d [label="%d U=%s E=%s"];' % (i,p, i, n, d, u, e)

  print "}"

regex = 'h={[^.]*\.ptr={([\d, ]*)},[^.]*\.is_iterator={([FALSETRU, ]*)},[^.]*\.succ={([\d, ]*)},[^.]*\.prev={([\d, ]*)},[^.]*\.data={([\d, ]*)},[^.]*\.dist={([\d, ]*)},[^.]*\.universal={([\d,{} ]*)},[^.]*\.nnodes=(\d+),[^.]*\.sorted={([\d, ]*)},[^.]*\.min={([\d, ]*)},[^.]*\.max={([\d, ]*)}'

cex = sys.stdin.read()

heaps = re.findall(regex, cex)

print "digraph {"

for i in range(0, len(heaps)):
  processHeap(heaps[i], i)

print "}"  
