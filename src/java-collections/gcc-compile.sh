#!/bin/bash

gcc -I ./ ./util.c ./abstract_transformers.c ./shakira.c $*
