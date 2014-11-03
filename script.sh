bzzt="63 127 255 511"
for i in $bzzt
do
    echo $i
    for j in `seq 1 10`
    do
        ./random_lts -n $i -b  0 > l01.dot
        ./random_lts -n $i -b $i > l02.dot
        TIME="%e" time ./relts_without_f --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0
        # time ./relts --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0 --pairs
        # time ./relts --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0 --relation
    done
done
for i in $bzzt
do
    echo $i
    for j in `seq 1 10`
    do
        ./random_lts -n $i -b  0 > l01.dot
        ./random_lts -n $i -b $i > l02.dot
        TIME="%e" time ./relts_with_f --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0
        # time ./relts --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0 --pairs
        # time ./relts --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0 --relation
    done
done
for i in $bzzt
do
    echo $i
    for j in `seq 1 10`
    do
        ./random_lts -c -n $i -b  0 > l01.dot
        ./random_lts -c -n $i -b $i > l02.dot
        TIME="%e" time ./relts_without_f --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0
        # time ./relts --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0 --pairs
        # time ./relts --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0 --relation
    done
done
for i in $bzzt
do
    echo $i
    for j in `seq 1 10`
    do
        ./random_lts -c -n $i -b  0 > l01.dot
        ./random_lts -c -n $i -b $i > l02.dot
        TIME="%e" time ./relts_with_f --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0
        # time ./relts --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0 --pairs
        # time ./relts --lts1 l01.dot --lts2 l02.dot -p 1 -q $((i+1)) -n 0 --relation
    done
done
