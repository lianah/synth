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
args[10]="-DNPROG=4 -DNPREDS=2 -DNSLACK=2"
expected[10]="VERIFICATION SUCCESSFUL"
pretty_args[10]="list copy it"


tests[11]="copy-unsafe.c"
args[11]="-DNPROG=4 -DNPREDS=2 -DNSLACK=2"
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
	# elif  [ "${fail/$expected}" = "$fail" ]; then
	#     # check that we fail due to the same reason
	#     printf " ${RED}[FAIL]${NC} $fail doesn't match expected: $EXPECTED\n"
	#     `cat $LOG_FILE | ./pretty-heap.py $PRETTY_ARGS | dot -Tpng > $HEAP_FILE`
	#     printf " Output heap in $HEAP_FILE\n"
	# else
	#     printf " ${GREEN}[SUCCESS]${NC}"
	#     `cat $LOG_FILE | ./pretty-heap.py $PRETTY_ARGS | dot -Tpng > $HEAP_FILE`
	#     printf " Output heap in $HEAP_FILE\n"
	#     # TODO Check that we can reproduce by compiling program
	# fi
	
    elif [ "$success" = "$EXPECTED" ]; then
	printf " ${GREEN}[SUCCESS]${NC} SAFE - Invariant holds. \n"
    else
	printf " ${RED}[FAIL]${NC} $success doesn't match expected: $EXPECTED\n"
    fi
	
    printf "$fail $success $time exit code $exit_code\n"
done
