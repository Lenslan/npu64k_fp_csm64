#!/usr/bin/env bash
#TODO: should use a single tcf + input link_cmd during ccac compilations
set -e

arc_cfg=npu_arc_se_ad1k_N64_fs_pg
#prj=${NPU_DEPS}/npu_arc/project_npu_arc_se_ad1k_N64_fs
if [ $# -ge 1 ]; then
  arc_cfg=$1
fi
prj=${NPU_DEPS}/npu_arc/project_$arc_cfg
if [ $# -ge 2 ]; then
  nsl=$2
fi
printf "arc_cfg: ${arc_cfg}\nprj    : $(basename ${prj})\nslices : ${nsl}" | tee README 2>&1

# l1arc
last_sl=$(( ${nsl}-1 ))
for sl in $(seq 0 1 $last_sl)
do
  sl_hex=$(printf "0x%02x000000" ${sl})
  printf "  sl: %2d   sl_hex: ${sl_hex}\n" $sl
  #cp -f ${prj}/build/tool_config/arc.tcf ./sl${sl}.tcf
  sed "s/SYSTEM0 : ORIGIN.*/SYSTEM0 : ORIGIN = ${sl_hex}, LENGTH = 0x01000000/" ${prj}/build/tool_config/arc.tcf > ./sl${sl}.tcf
done

# l2arc
l2=24
l2_hex=$(printf "0x%02x000000" ${l2})
printf "  l2: %2d   l2_hex: ${l2_hex}\n" $l2
#echo "  l2: $l2   l2_hex: ${l2_hex}"
#cp -f ${prj}/build/tool_config/arc.tcf ./arc.tcf
sed "s/SYSTEM0 : ORIGIN.*/SYSTEM0 : ORIGIN = ${l2_hex}, LENGTH = 0x01000000/" ${prj}/build/tool_config/arc.tcf > ./arc.tcf

# l2arc1 available for >=32K build
if [ $nsl -ge 8 ]; then
  l2=25
  l2_hex=$( printf "0x%02x000000" ${l2})
  printf "l2_1: %2d   l2_hex: ${l2_hex}\n" $l2
  #echo "l2_1: $l2 l2_1_hex: ${l2_hex}"
  #cp -f ${prj}/build/tool_config/arc.tcf ./arc.tcf
  sed "s/SYSTEM0 : ORIGIN.*/SYSTEM0 : ORIGIN = ${l2_hex}, LENGTH = 0x01000000/" ${prj}/build/tool_config/arc.tcf > ./arc1.tcf
fi

#cp -f arc.tcf arc1.tcf ../

