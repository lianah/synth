#!/bin/bash
./shakira.sh -D__CPROVER $* | ./mk-counterexample.py > counterexample.c
gcc -o debug.out -g -I ./ ./util.c ./abstract_transformers.c ./shakira-test.c ./counterexamples.c $*
./debug.out
# ../../tests/java-collections/set-const-safe/set-const.c -DNPROG=3 -DNPREDS=1
