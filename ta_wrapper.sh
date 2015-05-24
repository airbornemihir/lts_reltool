#!/bin/bash

MINPARAMS=2
if [ $# -lt "$MINPARAMS" ]
then
    echo
    echo "This script needs at least $MINPARAMS command-line arguments for ta1 and ta2!"
else
    
    calc < $1 > /dev/null 2> /dev/null
    mv /tmp/lts.dot /tmp/lts1.dot
    v1=`head -n 2 /tmp/lts1.dot | tail -n 1 | sed 's/;$//'`
    calc < $2 > /dev/null 2> /dev/null
    mv /tmp/lts.dot /tmp/lts2.dot
    v2=`head -n 2 /tmp/lts2.dot | tail -n 1 | sed 's/;$//'`
    if [ -n "$3" ];
    then
        if [ -n "$4" ];
        then
            bash -c "relts --lts1 /tmp/lts1.dot --lts2 /tmp/lts2.dot -p $v1 -q $v2 -n $3 -k $4"
        else
            bash -c "relts --lts1 /tmp/lts1.dot --lts2 /tmp/lts2.dot -p $v1 -q $v2 -n $3"
        fi
    else
        if [ -n "$4" ];
        then
            bash -c "relts --lts1 /tmp/lts1.dot --lts2 /tmp/lts2.dot -p $v1 -q $v2 -k $4"
        else
            bash -c "relts --lts1 /tmp/lts1.dot --lts2 /tmp/lts2.dot -p $v1 -q $v2"
        fi
    fi
fi  
