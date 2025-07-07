#!/usr/bin/env bash
set -xeo pipefail

sim_cores=${1:-0x00000000}
max_cycles=${2:-1000000}

echo "sim_cores: $sim_cores"
echo "max_cycles: $max_cycles"

# do nothing if sim_cores=0 and simulation will use the existing vcs_run.opt
if [[ $sim_cores -le 0 ]]; then
  exit 0
fi

# generate vcs_run.opt based on input parameters
max_l1cores=24
max_l2cores=2
l1core_id=0
l2core_id=0
core_id=0
cmd=""
l1_sim_cores=$(( (sim_cores & 0xffffff) ))
l2_sim_cores=$(( (sim_cores >> 24)      ))
l2_sim_cores=$(( (l2_sim_cores & 0x3)   ))
printf "l1_sim_cores: 0x%06x\n" $l1_sim_cores
printf "l2_sim_cores: 0x%0x\n"  $l2_sim_cores

#- l1cores
while [[ ${l1_sim_cores} -gt 0 ]]; 
do
  echo "l1_sim_cores: $l1_sim_cores"
  l1_sim_cores=$(( l1_sim_cores >> 1))
  cmd+=" +RUN_SLC${l1core_id}_ARC=1"
  l1core_id=$(( l1core_id+1 ))
done

#- l2cores
while [[ ${l2_sim_cores} -gt 0 ]]; 
do
  echo "l2_sim_cores: $l2_sim_cores"
  l2_sim_cores=$(( l2_sim_cores >> 1))
  if [[ ${l2core_id} -eq 0 ]]; then
    cmd+=" +RUN_L2_ARC=1"
  else
    cmd+=" +RUN_L2_ARC${l2core_id}=1"
  fi
  l2core_id=$(( l2core_id+1 ))
done

#-xm_hex and max_cycles
cmd+=" +XM_HEX=test.hex +MAX_CYCLE=${max_cycles}"
cmd=$(echo $cmd | sed 's/^[[:blank:]]*//g')

echo "$cmd" | tee vcs_run.opt

exit 0
