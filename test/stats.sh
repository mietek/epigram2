#!/bin/bash

## Grab the directory
# Because stuffs are stored in "./.measures/stats/${time}/"
if [ $# -eq 0 ]
then
    echo "Please provide the time at which the test suite was run."
    exit 1
fi
time=$1

## Go where the stuff is
cd "./.measures/stats/${time}/"
stats=`ls *.pig.stat`



## Extract the bits of direct interest
# Which are: allocated bytes, cpu time for Init, Mutator, and GC

echo -n "Extracting time and space statistics... "

for file in $stats
do
    for field in "bytes allocated" "init_cpu_seconds" "mutator_cpu_seconds" "GC_cpu_seconds"
    do
	data=`sed -ne 's/.*"'"$field"'", "\(.*\)".*/\1/p' $file`
	echo $data > $file.$(echo ${field} | sed -e 's/ /_/g')
    done
done

echo "Done."