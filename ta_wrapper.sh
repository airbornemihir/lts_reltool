#!/bin/bash
calc < $1 > /dev/null 2> /dev/null
mv /tmp/lts.dot /tmp/lts1.dot
v1=`head -n 2 /tmp/lts1.dot | tail -n 1 | sed 's/;$//'`
calc < $2 > /dev/null 2> /dev/null
mv /tmp/lts.dot /tmp/lts2.dot
v2=`head -n 2 /tmp/lts2.dot | tail -n 1 | sed 's/;$//'`
bash -c "relts --lts1 /tmp/lts1.dot --lts2 /tmp/lts2.dot -p $v1 -q $v2 -n 0"
