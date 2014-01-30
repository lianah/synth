#!/usr/bin/outputn

import re
import perfcounters as perf
import args

instpermre = re.compile('inst_perm={(.*?)}')
opspermre = re.compile('op_perm={(.*?)}')
outputre = re.compile('output_var=(\d*)')

binops = {
    0: "+",
    1: "-",
    2: "*",
    3: "/",
    6: "&",
    7: "|",
    8: "^",
    14: "<<",
    15: ">>",
    10: "=",
    11: "!=",
    13: "<=",
    12: "<"
}

unops = {
    9: "~"
}

nulops = {
    4: "1",
    5: "0"
}

def str2ints(s):
  ret = []

  if not s:
    return []

  for w in s.split(','):
    w = w.strip()
    w = w.replace('u', '')

    ret.append(int(w))

  return ret

class Prog(object):
  instperm = []
  invperm = []
  opsperm = []
  outvar = -1

  def __init__(self, instperm=[], opsperm=[], outvar=-1):
    self.instperm = instperm
    self.opsperm = opsperm
    self.outvar = outvar
    self.invperm = self.inv(instperm)

  def inv(self, instperm):
    if instperm:
      return [instperm.index(i) for i in xrange(max(instperm)+1)]

  def parse(self, output):
    for l in output:
      minsts = instpermre.search(l)
      mops = opspermre.search(l)
      moutvar = outputre.search(l)

      if minsts:
        self.instperm = str2ints(minsts.group(1))
        self.invperm = self.inv(self.instperm)

      if mops:
        self.opsperm = str2ints(mops.group(1))

      if moutvar:
        self.outvar = int(moutvar.group(1))

  def strarg(self, p):
    if p < args.args.args:
      return 'a%d' % (p+1)
    else:
      invperm = self.invperm
      a = invperm[p - args.args.args]
      return 't%d' % a

  def __str__(self):
    instperm = self.instperm
    opsperm = self.opsperm
    strinsts = []

    print instperm
    print opsperm

    for i in xrange(max(instperm) + 1):
      op = instperm[i]
      p1 = opsperm[op*2]
      p2 = opsperm[(op*2) + 1]

      if op in binops:
        strinsts.append("t%d = %s %s %s" % (i, self.strarg(p1),
          binops[op], self.strarg(p2)))
      elif op in unops:
        strinsts.append("t%d = %s %s" % (i, unops[op], self.strarg(p1)))
      elif op in nulops:
        strinsts.append("t%d = %s" % (i, nulops[op]))
      else:
        raise Exception("Couldn't parse instruction: (%d, %d, %d)" %
            (op, p1, p2))
  
    strinsts.append("return t%d" % self.outvar)

    return '\n'.join(strinsts)
