#!/bin/bash

tests[0]="javaset-const-safe.c"
args[0]="-DNPROG=1 -DNPREDS=2 -DNSETPROG=2"
expected[0]="VERIFICATION SUCCESSFUL"
pretty_args[0]="set"

tests[1]="javaset-const-unsafe.c"
args[1]="-DNPROG=1 -DNPREDS=2 -DNSETPROG=2"
expected[1]="INV_FAIL: Property entailment."
pretty_args[1]="set"

tests[2]="javaset-symbolic-safe.c"
args[2]="-DNPROG=1 -DNPREDS=2 -DNSETPROG=2"
expected[2]="VERIFICATION SUCCESSFUL"
pretty_args[2]="set"

tests[3]="javaset-symbolic-unsafe.c"
args[3]="-DNPROG=1 -DNPREDS=2 -DNSETPROG=2"
expected[3]="INV_FAIL: Inductive step."
pretty_args[3]="set"

tests[4]="javaset-list-copy-safe.c"
args[4]="-DNPROG=3 -DNSETPROG=2 -DNPREDS=11 -DNSLACK=2"
expected[4]="VERIFICATION SUCCESSFUL"
pretty_args[4]="set it"

tests[5]="javaset-list-copy-unsafe.c"
args[5]="-DNPROG=3 -DNSETPROG=2 -DNPREDS=1 -DNSLACK=2"
expected[5]="INV_FAIL:"
pretty_args[5]="set it"

tests[6]="apache_ListUtils-hashCodeForList-safe.c"
args[6]="-DNPROG=5"
expected[6]="VERIFICATION SUCCESSFUL"
pretty_args[6]="list1 list2 it1 it2"

tests[7]="apache_ListUtils-hashCodeForList-unsafe.c"
args[7]="-DNPROG=5"
expected[7]="INV_FAIL:"
pretty_args[7]="list1 list2 it1 it2"

tests[8]="apache_ListUtils-isEqualList-safe.c"
args[8]="-DNPROG=5"
expected[8]="VERIFICATION SUCCESSFUL"
pretty_args[8]="list1 list2 it1 it2"

tests[9]="apache_ListUtils-isEqualList-unsafe.c"
args[9]="-DNPROG=5"
expected[9]="INV_FAIL:"
pretty_args[9]="list1 list2 it1 it2"

tests[10]="guava_Ints-max-safe.c"
args[10]="-DNPROG=3"
expected[10]="VERIFICATION SUCCESSFUL"
pretty_args[10]="list it"

tests[11]="guava_Ints-max-unsafe.c"
args[11]="-DNPROG=4 -DNPREDS=1 -DNSLACK=2"
expected[11]="INV_FAIL:"
pretty_args[11]="list it"

tests[12]="guava_Ints-min-safe.c"
args[12]="-DNPROG=3"
expected[12]="VERIFICATION SUCCESSFUL"
pretty_args[12]="list it"

tests[13]="guava_Ints-min-unsafe.c"
args[13]="-DNPROG=3"
expected[13]="INV_FAIL:"
pretty_args[13]="list it"


# tests[0]="../../tests/java-collections/set-const2-safe.c"
# tests[0]="../../tests/java-collections/set-const3-safe.c"
# tests[0]="../../tests/java-collections/min-iterator-safe.c"
# tests[0]="../../tests/java-collections/pivot.c"
# tests[0]="../../tests/java-collections/reverse-pos-safe.c"

SHAKIRA="./shakira.sh "
TEST_PATH="../../tests/java-collections/"


RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

red_fail=${RED}[FAIL]${NC}
green_success=${GREEN}[SUCCESS]${NC}


for ((i=0;i<${#tests[@]};++i)); do
    LOG_FILE="$TEST_PATH${tests[i]}.log"
    HEAP_FILE="$TEST_PATH${tests[i]}.png"
    INPUT_FILE="$TEST_PATH${tests[i]}"
    ARGS="${args[i]}"
    PRETTY_ARGS="${pretty_args[i]}"
    EXPECTED="${expected[i]}"
	    
    CMD="$SHAKIRA $INPUT_FILE $ARGS  "
    printf "Running $CMD\n"
    `runlim -s 18000 -t 600 $CMD &> $LOG_FILE`
    exit_code=$?
    fail=`grep INV_FAIL $LOG_FILE`
    success=`grep "VERIFICATION SUCCESSFUL" $LOG_FILE`
    sat_time=`grep "Runtime decision procedure:" $LOG_FILE`
    symex_time=`grep "\[runlim\] time:" $LOG_FILE`
    memory=`grep "\[runlim\] space:" $LOG_FILE`

    # echo "grep \"[runlim] time:\" $LOG_FILE"
    
    if [ -z "$success" ]; then
	if [ -z "$fail" ]; then
	    # both strings cannot be empty
	    printf " ${RED}[FAIL]${NC} ERROR in output. \n"
	elif  [[ "$fail" == *"$EXPECTED"* ]]; then
	    printf " ${GREEN}[SUCCESS]${NC}"
	    `cat $LOG_FILE | ./pretty-heap.py $PRETTY_ARGS | dot -Tpng > $HEAP_FILE`
	    printf " Counterexample heap in $HEAP_FILE\n"
	    # TODO Check that we can reproduce by compiling program
	else
	    # check that we fail due to the same reason
	    printf " ${RED}[FAIL]${NC} $fail doesn't match expected: $EXPECTED\n"
	    `cat $LOG_FILE | ./pretty-heap.py $PRETTY_ARGS | dot -Tpng > $HEAP_FILE`
	    printf " Counterexample heap in $HEAP_FILE\n"
	fi
    elif [ "$success" = "$EXPECTED" ]; then
	printf " ${GREEN}[SUCCESS]${NC} SAFE - Invariant holds. \n"
    else
	printf " ${RED}[FAIL]${NC} $success doesn't match expected: $EXPECTED\n"
    fi
	
    printf "$fail $success $sat_time $symex_time $memory exit code $exit_code\n"
done
