#!/bin/bash

basedir="`dirname $0`"

./cbmc -DWIDTH=5 -DVERIF -I $basedir $basedir/util.c $basedir/abstract_transformers.c $basedir/shakira.c $*
