#!/bin/bash

tests[0]="cardinality-safe.c"
args[0]="-DNPROG=2 -DNPREDS=3"
expected[0]="VERIFICATION SUCCESSFUL"
pretty_args[0]="list"

tests[1]="cardinality-unsafe.c"
args[1]="-DNPROG=2 -DNPREDS=3"
expected[1]="INV_FAIL: Property entailment."
pretty_args[1]="list"

tests[2]="remove2-safe.c"
args[2]="-DNPROG=3 -DNPREDS=1"
expected[2]="VERIFICATION SUCCESSFUL"
pretty_args[2]="list it"


tests[3]="remove2-unsafe.c"
args[3]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[3]="INV_FAIL: Inductive step."
pretty_args[3]="list it"


tests[4]="remove-safe.c"
args[4]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[4]="VERIFICATION SUCCESSFUL"
pretty_args[4]="list it"

tests[5]="remove-unsafe.c"
args[5]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[5]="INV_FAIL:"
pretty_args[5]="list it"

tests[6]="set-const-safe.c"
args[6]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[6]="VERIFICATION SUCCESSFUL"
pretty_args[6]="list it"

tests[7]="set-const-unsafe.c"
args[7]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[7]="INV_FAIL:"
pretty_args[7]="list it"

tests[8]="copy2-safe.c"
args[8]="-DNPROG=4 -DNPREDS=2 -DNSLACK=2"
expected[8]="VERIFICATION SUCCESSFUL"
pretty_args[8]="list copy it"

tests[9]="copy2-unsafe.c"
args[9]="-DNPROG=4 -DNPREDS=2 -DNSLACK=2"
expected[9]="INV_FAIL:"
pretty_args[9]="list copy it"

tests[10]="copy-safe.c"
args[10]="-DNPROG=4 -DNPREDS=1 -DNSLACK=2"
expected[10]="VERIFICATION SUCCESSFUL"
pretty_args[10]="list copy it"


tests[11]="copy-unsafe.c"
args[11]="-DNPROG=4 -DNPREDS=1 -DNSLACK=2"
expected[11]="INV_FAIL:"
pretty_args[11]="list copy it"

tests[12]="reverse-safe.c"
args[12]="-DNPROG=5 -DNPREDS=1 -DNSLACK=2"
expected[12]="VERIFICATION SUCCESSFUL"
pretty_args[12]="list rev it it2"

tests[13]="reverse-unsafe.c"
args[13]="-DNPROG=5 -DNPREDS=1 -DNSLACK=3"
expected[13]="INV_FAIL:"
pretty_args[13]="list rev it it2"

tests[14]="add_to_sorted_list_safe.c"
args[14]="-DNPROG=2 -DNPREDS=1 -DNSLACK=1"
expected[14]="VERIFICATION SUCCESSFUL"
pretty_args[14]="list"

tests[15]="add_to_sorted_list_unsafe.c"
args[15]="-DNPROG=2 -DNPREDS=1 -DNSLACK=1"
expected[15]="INV_FAIL: Base case."
pretty_args[15]="list"

tests[16]="max-builtin-iterator-safe.c"
args[16]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[16]="VERIFICATION SUCCESSFUL"
pretty_args[16]="list it"

tests[17]="max-builtin-iterator-unsafe.c"
args[17]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[17]="INV_FAIL: Inductive step."
pretty_args[17]="list it"

tests[18]="filter-safe.c"
args[18]="-DNPROG=3 -DNPREDS=2 -DNSLACK=2"
expected[18]="VERIFICATION SUCCESSFUL"
pretty_args[18]="list it"

tests[19]="filter-unsafe.c"
args[19]="-DNPROG=3 -DNPREDS=2 -DNSLACK=2"
expected[19]="INV_FAIL: Inductive step."
pretty_args[19]="list it"

tests[20]="pivot-safe.c"
args[20]="-DNPROG=5 -DNPREDS=2 -DNSLACK=2"
expected[20]="VERIFICATION SUCCESSFUL"
pretty_args[20]="list less great it"

tests[21]="pivot-unsafe.c"
args[21]="-DNPROG=5 -DNPREDS=2 -DNSLACK=2"
expected[21]="INV_FAIL: Inductive step."
pretty_args[21]="list less great it"

tests[22]="selection-sort-inner-loop-safe.c"
args[22]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[22]="VERIFICATION SUCCESSFUL"
pretty_args[22]="list it"

tests[23]="selection-sort-inner-loop-unsafe.c"
args[23]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[23]="INV_FAIL: Inductive step."
pretty_args[23]="list it"

tests[24]="selection-sort-outer-loop-safe.c"
args[24]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[24]="VERIFICATION SUCCESSFUL"
pretty_args[24]="list it"

tests[25]="selection-sort-outer-loop-unsafe.c"
args[25]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[25]="INV_FAIL: Inductive step."
pretty_args[25]="list it"

tests[26]="quicksort-first-loop-safe.c"
args[26]="-DNPROG=5 -DNPREDS=1 -DNSLACK=2"
expected[26]="VERIFICATION SUCCESSFUL"
pretty_args[26]="list less greater it"

tests[27]="quicksort-first-loop-unsafe.c"
args[27]="-DNPROG=5 -DNPREDS=1 -DNSLACK=2"
expected[27]="INV_FAIL: Inductive step."
pretty_args[27]="list less greater it"

tests[28]="quicksort-second-loop-safe.c"
args[28]="-DNPROG=5 -DNPREDS=1 -DNSLACK=2"
expected[28]="VERIFICATION SUCCESSFUL"
pretty_args[28]="list less greater it"

tests[29]="quicksort-second-loop-unsafe.c"
args[29]="-DNPROG=5 -DNPREDS=1 -DNSLACK=2"
expected[29]="INV_FAIL: Inductive step."
pretty_args[29]="list less greater it"

tests[30]="implication-safe.c"
args[30]="-DNPROG=4 -DNPREDS=3"
expected[30]="VERIFICATION SUCCESSFUL"
pretty_args[30]="list it1 it2"

tests[31]="implication-unsafe.c"
args[31]="-DNPROG=4 -DNPREDS=3"
expected[31]="INV_FAIL: Property entailment."
pretty_args[31]="list it1 it2"

tests[32]="set-position-const-safe.c"
args[32]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[32]="VERIFICATION SUCCESSFUL"
pretty_args[32]="list it"

tests[33]="set-position-const-unsafe1.c"
args[33]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[33]="INV_FAIL: Inductive step."
pretty_args[33]="list it"

tests[34]="set-position-const-unsafe2.c"
args[34]="-DNPROG=3 -DNPREDS=1 -DNSLACK=1"
expected[34]="INV_FAIL: Property entailment."
pretty_args[34]="list it"

tests[35]="remove2-position-safe.c"
args[35]="-DNPROG=2 -DNPREDS=1 -DNSLACK=1"
expected[35]="VERIFICATION SUCCESSFUL"
pretty_args[35]="list"

tests[36]="remove2-position-unsafe.c"
args[36]="-DNPROG=2 -DNPREDS=1 -DNSLACK=1"
expected[36]="INV_FAIL: Property entailment."
pretty_args[36]="list"

tests[37]="pivot-position-safe.c"
args[37]="-DNPROG=4 -DNPREDS=2 -DNSLACK=2"
expected[37]="VERIFICATION SUCCESSFUL"
pretty_args[37]="list less great"

tests[38]="pivot-position-safe.c"
args[38]="-DNPROG=4 -DNPREDS=2 -DNSLACK=2"
expected[38]="INV_ERROR: Inductive step."
pretty_args[38]="list less great"

tests[39]="filter-position-safe.c"
args[39]="-DNPROG=4 -DNPREDS=2 -DNSLACK=2"
expected[39]="VERIFICATION SUCCESSFUL"
pretty_args[39]="list less great"

tests[40]="filter-position-unsafe.c"
args[40]="-DNPROG=4 -DNPREDS=2 -DNSLACK=2"
expected[40]="INV_ERROR: Inductive step."
pretty_args[40]="list less great"


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
    `$CMD &> $LOG_FILE`
    exit_code=$?
    fail=`grep INV_FAIL $LOG_FILE`
    success=`grep "VERIFICATION SUCCESSFUL" $LOG_FILE`
    time=`grep "Runtime decision procedure:" $LOG_FILE`
    
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
	
    printf "$fail $success $time exit code $exit_code\n"
done
