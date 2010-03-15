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

## Quiet flag:
# 0: verbose
# 1: quiet
quiet=0
if [ $# -le 1 ]
then
    if [ "$1" = "-q" ]
    then
	quiet=1
    fi
fi

## Test cases:
if [ $# -eq 0 ] || ( [ $# -eq 1 ] && [ $quiet -eq 1 ] )
then
    scripts=`ls *.pig`
else
    scripts=$@
fi

## Time
time=`date +%Y%m%d_%H%M`

## Check if we have RTS support for:
#   * coverage with HPC
#   * collect statistics on GC and time
advanced=0
if [ -f "../src/BUILD_TEST" ]
then
    advanced=1

    ## Ensure that measures can be stored
    mkdir -p "./.measures/hpc/${time}" \
	     "./.measures/stats/${time}" 

fi

## Check if we have RTS support for profiling
profiling=0
if [ -f "../src/BUILD_PROFILE" ]
then
    profiling=1

    ## Ensure that measures can be stored
    mkdir -p "./.measures/prof/${time}"
fi

## RTS option(s)
PIG_OPTS=""


## Run the test cases
for script in $scripts
do
    if [ -f "${script}.disabled" ]
    then 
	echo -e "$disabled $script is disabled"
	continue
    fi
    # echo -n "Running test $script..."
    if [ $advanced -eq 1 ]
    then
	PIG_OPTS="+RTS -t./.measures/stats/${time}/${script}.stat --machine-readable -RTS"
    elif [ $profiling -eq 1 ]
    then
	PIG_OPTS="+RTS -p -RTS"
    fi
    ../src/Pig $PIG_OPTS --check "$script" &> ".tests/$script.log"    
    if [ $advanced -eq 1 ]
    then
	mv "./Pig.tix" "./.measures/hpc/${time}/${script}.tix"
    elif [ $profiling -eq 1 ]
    then
        mv "./Pig.prof" "./.measures/prof/${time}/${script}.prof"
    fi
    # echo " Done."
    if [ ! -f "results/$script.log" ]
    then
	echo -e "$undefined Please provide the desired output for $script"
    else
	if ! diff -u "results/$script.log" ".tests/$script.log" > ".tests/$script.diff"
	then
	    echo -e "$failed $script does not match the expected output"
	    status=1
	    if [ $quiet -eq 0 ]
	    then
		cat ".tests/$script.diff"
	    fi
	else
	    echo -e "$passed $script looks alright!"
	fi
    fi
done

echo ""

## Delegate post-processing of measurements
if [ $advanced -eq 1 ] 
then
  ./hpc.sh $time
  ./stats.sh $time
fi

if [ $advanced -eq 1 ]
then

    if [ -f "./.measures/hpc/${time}/all.coverage" ]
    then
	
	echo ""
	echo "Code coverage:"
	echo "=============="

	cat "./.measures/hpc/${time}/all.coverage"

    fi

    echo ""
    echo "Performance variation:"
    echo "======================"
    ./report_stats.sh

fi

exit $status