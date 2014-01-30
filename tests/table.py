#!/usr/bin/python

import cPickle

def make_graph(kalashnikov, pldi, icse, icse_semibiased):
  print "\\begin{tabular}{l||rrc|rrrc|rr}"
  print "Problem & \multicolumn{3}{c}{\\sc PLDI Brahma} & \multicolumn{4}{|c}{ICSE Brahma} & \multicolumn{2}{|c}{\\sc Kalashnikov} \\\\"
  print "        & Runtime & \#Lines & Aut. & Random & Semibiased & \#Lines & Aut. & Runtime & \#Lines \\\\"

  print "\\hline"
  print "\\hline"

  keys = set(kalashnikov.keys() + pldi.keys() + icse.keys())
  ns = sorted(int(k) for k in keys)

  for n in ns:
    k = str(n)

    alltimes = []
    insts = []

    if k in pldi:
      (cnt, times) = pldi[k]
      pldit = times['_']
      pldin = cnt['insts']
      pldiaut = cnt['automatic']

      alltimes.append(pldit)
      insts.append(pldin)
    else:
      pldit = None

    if k in kalashnikov:
      (cnt, times) = kalashnikov[k]
      kalt = times['_']
      kaln = cnt['insts']

      alltimes.append(kalt)
      insts.append(kaln)
    else:
      kalt = None
    
    if k in icse:
      (cnt, time) = icse[k]
      icset = time['_']
      icsen = cnt['insts']

      alltimes.append(icset)

      (cnt, time) = icse_semibiased[k]
      semit = time['_']
      icseaut = cnt['automatic']

      alltimes.append(semit)
      insts.append(icsen)
    else:
      icset = None

    mintime = min(t for t in alltimes if t > 0)
    mininsts = min(insts)

    line = "p%s & " % k


    def f(t, insts):
      ret = ''

      if t is None:
        ret += "N/A &"
      elif t == mintime:
        ret += "{\\bf %.02fs} &" % t
      elif t < 0:
        ret  += "T/O &"
      else:
        ret += "%.02fs &" % t

      if t < 0:
        ret += '-- &'
      elif insts == mininsts:
        ret += '{\\bf %d} &' % insts
      else:
        ret += '%d &' % insts

      return ret

    line += f(pldit, pldin)

    if not pldiaut:
      line += ' \\xmark & '
    else:
      line += ' & '

    def g(t, semit, insts):
      ret = ''
      
      if t is None:
        ret += "N/A &"
      elif t == mintime:
        ret += "{\\bf %.02fs} &" % t
      elif t < 0:
        ret  += "T/O &"
      else:
        ret += "%.02fs &" % t

      if t is None:
        ret += " N/A &"
      elif semit == mintime:
        ret += " {\\bf %.02fs} & " % semit
      elif semit < 0:
        ret += " T/O & "
      else:
        ret += " %.02fs & " % semit

      if t < 0:
        ret += '-- &'
      elif insts == mininsts:
        ret += '{\\bf %d} &' % insts
      else:
        ret += '%d &' % insts

      return ret

    line += g(icset, semit, icsen)

    if not icseaut:
      line += ' \\xmark & '
    else:
      line += ' & '

    line += f(kalt, kaln)

    line = line[:-1]

    print "%s\\\\" % line

  print "\\end{tabular}"

def load(fname):
  f = open(fname, 'rb')
  ret = cPickle.load(f)
  f.close()

  return ret

if __name__ == '__main__':
  pldi = load('processed/brahma.stats')
  icse = load('processed/icse.stats')
  semi = load('processed/icse_semibiased.stats')
  kalashnikov = load('processed/const.stats')

  make_graph(kalashnikov, pldi, icse, semi)