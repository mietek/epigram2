#!/bin/bash

## List all collected stats, by time
# (soonest first)
stats=(`ls -t .measures/stats/`)


## Quit if 1st run
# We report relative variations, so we need at least 2 measurements
if [ ${#stats[*]} -le 1 ]
then
    echo "Need at least two measurements to report an evolution."
    exit 1
fi


## Get the time of the last and previous one
now=${stats[0]}
before=${stats[1]}

## Initialise counters
counter=0
space_total=0
time_total=0

## For each current measure, compute variation
echo -n "Computing performance variations... "

for stat in `ls .measures/stats/${now}/*.pig.stat.*`
do
    test=`echo $(basename $stat) | sed -ne 's/\(.*\)\..*/\1/p'`
    measure=`echo $stat | sed -ne 's/.*\.\(.*\)/\1/p'`
    old_stat=".measures/stats/${before}/${test}.${measure}"

    if [ ! -f $old_stat ]
    then
	continue;
    fi

    counter=$(($counter + 1));

    now_value=`cat $stat`
    before_value=`cat $old_stat`

    diff_value=`echo "$before_value - $now_value" | bc -l`

    case "$measure" in
	"bytes_allocated" ) 
	    space_total=`echo "$space_total + $diff_value" | bc -l`
	    ;;
	*)
	    time_total=`echo "$time_total + $diff_value" | bc -l`
	    ;;
    esac

done

echo "Done."
echo ""

## Sum up the result, if possible
if [ $counter -ne 0 ] 
then
    time_var=`echo "scale=1; $time_total / $counter" | bc -l`
    space_var=`echo "scale=0; ($space_total / $counter) / 1024" | bc -l`

    echo -n "Time variation: "
    if [[ $time_var != -* ]] 
    then
	echo -n "+"
    fi
    echo -n $time_var
    echo " seconds."

    echo -n "Space variation: "
    if [[ $space_var != -* ]] 
    then
	echo -n "+"
    fi
    echo -n $space_var
    echo " kbytes."
fi