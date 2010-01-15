#!/bin/bash



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
	echo -e "\e[00;34m[UNDEFINED]\e[00m Please provide the desired output for $script"
    else
	if ! diff -u "results/$script.log" ".tests/$script.log" > ".tests/$script.diff"
	then
	    echo -e "\e[00;31m[FAILED]\e[00m $script does not match the expected output"
	    cat ".tests/$script.diff"
	else
	    echo -e "\e[00;32m[PASSED]\e[00m $script looks alright!"
	fi
    fi
done