#!/bin/bash
pwd
vcs_run_opt=vcs_run.opt
mydir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [[ -n "${NPU_HOME}" ]]; then
  rls=$NPU_HOME/build
else
  rls=$NPU_HOME_RLS
fi
has_l2=`grep -m1 -w "NPU_HAS_L2ARC" $rls/build_config.mk | sed s/[[:space:]]//g | sed 's/^.*=//g'`
duo_l2=`grep -m1 -w "DUO_L2ARC"     $rls/build_config.mk | sed s/[[:space:]]//g | sed 's/^.*=//g'`
echo "rls:$rls has_l2:$has_l2 duo_l2:$duo_l2"

l1present=0
l2present=0
GUI=0
mdb_flags="-rascal -nogoifmain -Xnodetect -prop=init_csm=0"
# FIXME: see CPU process allocations in connect_fast_rascal, to be aligned with coreid allocations
slc_pset_base=$(($has_l2+$duo_l2+1))
echo "has_l2:$has_l2 duo_l2:$duo_l2 slc_pset_base:$slc_pset_base"
exec_list=""

mdb_exe() { echo "mdb $@" ; mdb "$@" ; }

if [ ! -f $vcs_run_opt ] ; then
    echo "Error: VCS option file for test not found - $vcs_run_opt"
    exit 1
fi

if [ ${GUI} -eq 1 ]; then
    args=" -gui"
else
    args=" -cl -off=cr_for_more"
fi
#args="$args -cmd=\"read ./mdb.cmd\""

if grep -q "RUN_L2_ARC=1" $vcs_run_opt; then
    mdb_exe -psetname=NL2_0 -pset=1 $mdb_flags ${PWD}/outs/l2.elf
	exec_list="$exec_list,NL2_0"
    l2present=1
fi
if grep -q "RUN_L1_ALL=1" $vcs_run_opt; then
    cnt=$slc_pset_base
	slc_id=0
    for i in outs/sl*
    do
        mdb_exe -psetname=NL1_$slc_id -pset=$cnt $mdb_flags ${PWD}/$i
		cnt=$(( $cnt+1 ))
	    exec_list="$exec_list,NL1_${slc_id}"
		slc_id=$(( $slc_id+1 ))
        l1present=1
    done
fi
if grep -q "RUN_SLC0_ARC=1" $vcs_run_opt; then
    mdb_exe -psetname=NL1_0 -pset=$slc_pset_base $mdb_flags ${PWD}/outs/sl0.elf
	exec_list="$exec_list,NL1_0"
    l1present=1
fi

# trim exec_list
exec_list=${exec_list:1}

#conv single core test
if [[ $l2present -eq 0 ]] && [[ $l1present -eq 1 ]]; then
    mdb_exe -multifiles=${exec_list} -OK $args -cmd="read mdb.cmd" | tee -a simv.log
    #mdb_exe -multifiles=${exec_list} -run -OK $args
fi
if [[ $l2present -eq 1 ]] && [[ $l1present -eq 0 ]]; then
    mdb_exe -multifiles=${exec_list} -OK $args -cmd="read mdb.cmd" | tee -a simv.log
    #mdb_exe -multifiles=${exec_list} -run -OK $args
fi
if [[ $l2present -eq 1 ]] && [[ $l1present -eq 1 ]]; then
    mdb_exe -multifiles=${exec_list} -OK $args -cmd="read mdb.cmd" | tee -a simv.log
    #mdb_exe -multifiles=${exec_list} -run -OK $args
fi

