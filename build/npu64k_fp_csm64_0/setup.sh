#!/usr/bin/env bash
export NCONFIG=npu64k_fp_csm64_0

export NPU_HOME_RLS=`pwd`
#export NPU_DEPS_RLS=${NPU_HOME_RLS}/npu_deps
export NCORES_HOST=`grep -c '^processor' /proc/cpuinfo`
if [ -z "$NPU_RTL_SIMULATOR" ] ; then
  export NPU_RTL_SIMULATOR=0
fi

# vcs
if [[ $NPU_RTL_SIMULATOR -eq 0 ]]; then
  which vcs > /dev/null 2>&1
  if [[ $? -ne 0 ]]; then
      echo "ERROR: vcs cannot be found in ${PATH}"
  fi
  
  if [ -z "$SYNOPSYS" ] ; then
      echo "ERROR: \$SYNOPSYS cannot be found in the environment"
  fi
fi

#xcelium
if [[ $NPU_RTL_SIMULATOR -eq 1 ]]; then
  which xrun > /dev/null 2>&1
  if [[ $? -ne 0 ]]; then
      echo "ERROR: xrun cannot be found in ${PATH}"
  fi
  
  if [ -z "$SYNOPSYS" ] ; then
      echo "ERROR: \$SYNOPSYS cannot be found in the environment"
  fi
  export LD_LIBRARY_PATH=${LD_LIBRARY_PATH}:${VERDI_HOME}/share/PLI/IUS/LINUX64/boot:${VERDI_HOME}/share/PLI/IUS/LINUX64

  ## For simulations with MDB connected
  #if [[ -n "$ARCHITECT_ROOT" && -f "$ARCHITECT_ROOT/lib/linux_x86_64/libarc-vcs-pli-verilog.so" ]] ; then
  #    export NPU_VCS_PLI=$ARCHITECT_ROOT/lib/linux_x86_64
  #else
  #    export NPU_VCS_PLI=$NPU_HOME_RLS/lib
  #fi
  #if [ -z "$LD_LIBRARY_PATH" ] ; then
  #    export LD_LIBRARY_PATH=$NPU_VCS_PLI
  #else
  #    export LD_LIBRARY_PATH=$NPU_VCS_PLI:${LD_LIBRARY_PATH}
  #fi
fi

# modelsim


# For simulations with racal models
if [[ -n "$ARCHITECT_ROOT" ]] ; then
    export NPU_VCS_PLI=$ARCHITECT_ROOT/lib/linux_x86_64
else
    export NPU_VCS_PLI=$NPU_HOME_RLS/lib
fi
if [ -z "$LD_LIBRARY_PATH" ] ; then
    export LD_LIBRARY_PATH=$NPU_VCS_PLI
else
    export LD_LIBRARY_PATH=$NPU_VCS_PLI:${LD_LIBRARY_PATH}
fi
