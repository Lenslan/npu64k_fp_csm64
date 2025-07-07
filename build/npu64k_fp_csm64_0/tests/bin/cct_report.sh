#!/bin/bash
mydir="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

#set -x
tests=$1
seed_dir=${2:-xxx}
regr_en=${3:-0}





total_cnt=0
fail_cnt=0
msg=""

for t in $tests; 
do 
    total_cnt=$(($total_cnt+1))

    if [ $regr_en -eq 1 ]; then
    log=$t/$seed_dir.log
    rpt=$t/$seed_dir.report
    else
    log=$t/simv.log
    rpt=$t/sim.report
    fi

    if [ -f $log ]; then
        $mydir/check_sim_result.sh $log >& $rpt 
        if [ $? -ne 0 ]; then
            fail_cnt=$(($fail_cnt+1))
            msg+="$t : FAIL, please check report($rpt) and log($log) \\n"
        fi
    else
        msg+="$t : FAIL, log($log) not found \\n"
        fail_cnt=$(($fail_cnt+1))
    fi
done


# add a results .PASS file
if [ -f .PASS ]; then
  rm -f .PASS
fi

if [ $fail_cnt -eq 0 ]; then
    echo "==================================================================================="
    echo "PASS: All of $total_cnt tests are passed"
    echo "==================================================================================="
	touch .PASS
    printf "$msg"
else
    echo "==================================================================================="
    echo "FAIL: $fail_cnt of $total_cnt tests failed, please check the following failed tests"
    echo "==================================================================================="
    printf "$msg"
    exit 100
fi

