#!/bin/bash

failed="[FAILED]"
undefined="[UNDEFINED]"
passed="[PASSED]"
disabled="[DISABLED]"

case ${TERM} in
        dumb*) # emacs shell is "dumb"
	# no color for the dumbs
        ;;
        *)
	# otherwise, assume that we have colors
	failed="\e[00;31m${failed}\e[00m"
	undefined="\e[00;34m${undefined}\e[00m"
	passed="\e[00;32m${passed}\e[00m"
	disabled="\e[00;35m${disabled}\e[00m"
        ;;
esac

## Check that Pig is nearby
if [ ! -f "../src/Pig" ]
then
    echo "Pig is absent. Please 'make' it."
    exit 2
fi

## Make a clean cache directory 
if [ -d ".tests" ]
then
    rm -fR ".tests"
fi
mkdir ".tests"

## Status:
# 0: success
# 1: at least one test failed
# 2: no Pig binary
status=0

## Run the test cases
for script in `ls *.pig`
do
    if [ -f "${script}.disabled" ]
    then 
	echo -e "$disabled $script is disabled"
	continue
    fi
    # echo -n "Running test $script..."
    ../src/Pig --check "$script" > ".tests/$script.log"
    # echo " Done."
    if [ ! -f "results/$script.log" ]
    then
	echo -e "$undefined Please provide the desired output for $script"
    else
	if ! diff -u "results/$script.log" ".tests/$script.log" > ".tests/$script.diff"
	then
	    echo -e "$failed $script does not match the expected output"
	    status=1
	    cat ".tests/$script.diff"
	else
	    echo -e "$passed $script looks alright!"
	fi
    fi
done

exit $status