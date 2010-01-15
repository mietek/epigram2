#!/bin/bash

failed="[FAILED]"
undefined="[UNDEFINED]"
passed="[PASSED]"

case ${TERM} in
        dumb*) # emacs shell is "dumb"
	# no color for the dumbs
        ;;
        *)
	# otherwise, assume that we have colors
	failed="\e[00;31m${failed}\e[00m"
	undefined="\e[00;34m${undefined}\e[00m"
	passed="\e[00;32m${passed}\e[00m"
        ;;
esac

## Check that Pig is nearby
if [ ! -f "../src/Pig" ]
then
    echo "Pig is absent. Please 'make' it."
    exit
fi

## Make a clean cache directory 
if [ -d ".tests" ]
then
    rm -fR ".tests"
fi
mkdir ".tests"

## Run the test cases
for script in `ls *.pig`
do
    # echo -n "Running test $script..."
    ../src/Pig --check "$script" > ".tests/$script.log"
    # echo " Done."
    if [ ! -f "results/$script.log" ]
    then
	echo -e "$undefined Please provide the desired output for $script"
    else
	if ! diff -u "results/$script.log" ".tests/$script.log" > ".tests/$script.diff"
	then
	    echo -e "\e[00;31m[FAILED]\e[00m $script does not match the expected output"
	else
	    echo -e "$passed $script looks alright!"
	fi
    fi
done