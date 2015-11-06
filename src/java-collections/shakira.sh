#!/bin/bash

basedir="`dirname $0`"

./cbmc -DWIDTH=6 -D__CPROVER -I $basedir $basedir/util.c $basedir/abstract_transformers.c $basedir/shakira.c $*
