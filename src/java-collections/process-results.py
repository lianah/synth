#!/usr/bin/python

import argparse
import re
import sys
import string

class Result:
    def __init__(self, status, sat_time, symex_time):
        self.status = status
        self.sat_time = sat_time
        self.symex_time = symex_time

    def __str__(self):
        res = "(status: "+self.status + ", " \
              " sat_time: "+str(self.sat_time) + ", " \
              " symex_time: "+str(self.symex_time) +")"
        return res

class SolverToResult:
    def __init__(self):
        self.table = {} # Solver => (safe_result, unsafe_result)

    def addSafeResult(self, solver, result):
        if (solver in self.table):
            (res1, res2) = self.table[solver]
            assert (res1 == None)
            self.table[solver] = (result, res2)
        else:
            self.table[solver] = (result, None)

    def addUnsafeResult(self, solver, result):
        if (solver in self.table):
            (res1, res2) = self.table[solver]
            assert (res2 == None)
            self.table[solver] = (res1, result)
        else:
            self.table[solver] = (None, result)
        
    def getResult(self, solver):
        assert (solver in self.table)
        return self.table[solver]

        

class ResultsTable:
    def __init__(self):
        self.table = {} # problem => SolverToResult

    def addSafeResult(self, problem, solver, res):
        if (problem in self.table):
            pb_res = self.table[problem]
        else:
            pb_res = SolverToResult()
            
        pb_res.addSafeResult(solver, res)
        self.table[problem] = pb_res

    def addUnsafeResult(self, problem, solver, res):
        if (problem in self.table):
            pb_res = self.table[problem]
        else:
            pb_res = SolverToResult()
            
        pb_res.addUnsafeResult(solver, res)
        self.table[problem] = pb_res
        
    def getSafeResult(self, solver, problem):
        assert solver in self.solvers
        pb_res = self.table[problem]
        (res, _ ) = pb_res.getResult(solver)
        return res

    def getUnsafeResult(self, solver, problem):
        assert solver in self.solvers
        pb_res = self.table[problem]
        ( _, res) = pb_res.getResult(solver)
        return res

    def printTable(self, name1, name2):
        for pb in self.table:
            ress = self.table[pb]
            (res1_safe, res1_unsafe) = ress.getResult(name1)
            (res2_safe, res2_unsafe) = ress.getResult(name2)
            print pb, " ", res1_safe.status, " ", res1_safe.sat_time, " ", res1_safe.symex_time, " ", res1_unsafe.status, " ", res1_unsafe.sat_time, " ", res1_unsafe.symex_time, " ", res2_safe.status, " ", res2_safe.sat_time, " ", res2_safe.symex_time," ", res2_unsafe.status, " ", res2_unsafe.sat_time, " ", res2_unsafe.symex_time  
        

parser = argparse.ArgumentParser(description='Results file1 file2.')
parser.add_argument('-f','--first',type=str,
                    help='first')

parser.add_argument('-s','--second',type=str,
                    help='second')

args = parser.parse_args()
file1=args.first
file2= args.second


def processName(filename):
    index = string.find(filename, "unsafe")
    if index > 0:
        name = filename[0:index-1]
        return (name, False)
    index = string.find(filename, "safe")
    assert (index > 0)
    name = filename[0:index-1]
    return (name, True)

def readFromFile(fname, name, results):
    f = open(fname, 'r+')
    line = "aa"
    while line :
        line = f.readline()
        if not line:
            return
        # line has file name
        file_name = re.findall("tests/java-collections/(.*\.c)", line)
        (problem, safe) = processName(file_name[0])
        # print problem, " ", safe

        line = f.readline()
        status = re.findall("(\[SUCCESS\]|\[FAIL\])", line)
        # print status

        line = f.readline()
        line = line.replace('\t',"")
        times = re.findall("Runtime decision procedure: ([\d\.]*)s.*\[runlim] time:([\d\.]*) seconds \[runlim\] space:([\d\.]*)", line)
        # print times

        res = Result(status[0], times[0][0], times[0][1])
        
        if (safe):
            results.addSafeResult(problem, name, res)
        else:
            results.addUnsafeResult(problem, name, res)
        
        # status 
    
    f.close()


table = ResultsTable()    
readFromFile(file1, "SLDH", table)
readFromFile(file1, "SLDH2", table)
table.printTable("SLDH", "SLDH2")
# readFromFile(file2, "SLDH+sh")
