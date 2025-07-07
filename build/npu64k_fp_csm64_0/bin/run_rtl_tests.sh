#!/usr/bin/env bash
set -x
mydir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
#
# This script runs a list of sanity tests to make sure that RTL changes will not break anything.
#
if [ -z "$NPU_HOME" ]; then
    cd $mydir/../../../
    . setup.sh
fi
if [ -z $NCONFIG ]; then
    [ -z $NPU_DEPS ] && export NPU_DEPS="${NPU_HOME}/npu_deps"
    export NCONFIG=nu4500.novpx
    [ -d "$NPU_HOME/build/config" ] || make config
fi
[ -e "$NPU_HOME/build/sim/simv" ] || make -C $NPU_HOME/build build

set -e

# RTL test based on l1arc RTL with a tb for core_chip
cd ${NPU_HOME}/build/tests/ccts
if [ $# -ge 1 ]; then
  make build -j20 && make run SIMV=$1 -j20
else
  make build -j 20 && make run -j 20
fi
make report

## test based on l1arc DPI with single slice tb
#cd ${NPU_HOME}/verif/test_bench/run; make mcomp mtest MTEST=${NPU_HOME}/arch/npu_slice/regression/S15_slice_addr/test.cpp mrun
##cd ${NPU_HOME}/verif/tests/conv_test; make -f ../Makefile hex sim
##cd ${NPU_HOME}/verif/tests/l1arc_access_accel; make -f ../Makefile hex sim
##cd ${NPU_HOME}/verif/tests/l1arc_access_scm; make -f ../Makefile hex sim
##cd ${NPU_HOME}/verif/tests/l1arc_access_xm; make -f ../Makefile hex sim
##cd ${NPU_HOME}/verif/tests/l2arc_access_cln_aux; make -f ../Makefile hex sim
##cd ${NPU_HOME}/verif/tests/l2arc_access_xm; make -f ../Makefile hex sim

