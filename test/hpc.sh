#!/bin/bash

## Grab the directory
# Because stuffs are stored in "./.measures/hpc/${time}/"
if [ $# -eq 0 ]
then
    echo "Please provide the time at which the test suite was run."
    exit 1
fi
time=$1

## Go where the stuff is
cd "./.measures/hpc/${time}/"
tixes=`ls *.tix`


## Per-test case report (could be useful?):
#for file in $tixes
#do
#    hpc report --srcdir "../src/" $file > $(basename $file).coverage
#done



## Global coverage

echo -n "Computing global code coverage... "

hpc sum *.pig.tix --output=all.tix
hpc report --srcdir "../../../../src/" all.tix > all.coverage

echo "Done."