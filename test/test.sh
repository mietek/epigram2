#!/bin/sh



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
    echo -n "Running test $script..."
    ../src/Pig --check "$script" > ".tests/$script.log"
    echo " Done."
    if [ ! -f "results/$script.log" ]
    then
	echo "[UNDEFINED] Please provide the desired output for $script"
    else
	if ! diff ".tests/$script.log" "results/$script.log" > /dev/null 
	then
	    echo "[FAILED] $script does not match the expected output"
	fi
    fi
done