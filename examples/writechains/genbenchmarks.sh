#!/bin/bash
for ((a=0;a<=1;a+=1))
do
  inc=1
  if [[ $a -eq 1 ]]; then
    aarg="-a"
    limit=100
  else
    aarg=""
    limit=500
  fi
  for ((numbits=2;numbits<=$limit;numbits+=$inc))
  do
    header=1
    if [[ $numbits -lt 10 ]]; then
      numbitsstring="00"$numbits
    elif [[ $numbits -lt 100 ]]; then
      numbitsstring="0"$numbits
    else
      numbitsstring=$numbits
    fi
    if [[ $a -eq 1 ]]; then
      filename=wchains$numbitsstring"ue.smt"
    else
      filename=wchains$numbitsstring"se.smt"
    fi
    ./writechains $aarg $numbits | boolector -rwl 0 -ds | while read line
    do
      if [[ $header -eq 1 ]]; then
        echo "(benchmark $filename" > $filename
        echo ":source {" >> $filename
        echo "This benchmark generates write chain permutations and tries to show" >> $filename
        echo "via extensionality that they are equal." >> $filename
        echo "" >> $filename
        echo -n "Contributed by Armin Biere " >> $filename
        echo "(armin.biere@jku.at)." >> $filename
        echo "}" >> $filename
        if [[ $a -eq 1 ]]; then
          echo ":status unsat" >> $filename
        else
          echo ":status sat" >> $filename
        fi
        echo ":category { crafted }" >> $filename
        header=0
      else
        echo $line >> $filename
      fi
    done
    if [[ $numbits -eq 20 ]]; then
      inc=2
    elif [[ $numbits -eq 50 ]]; then
      inc=5 
    elif [[ $numbits -eq 100 ]]; then
      inc=10
    elif [[ $numbits -eq 200 ]]; then
      inc=50
    fi
  done
done
