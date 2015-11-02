#!/bin/bash

gcc -g -I ./ ./util.c ./abstract_transformers.c ./shakira-test.c ./counterexamples.c $*
# ../../tests/java-collections/set-const-safe/set-const.c -DNPROG=3 -DNPREDS=1
