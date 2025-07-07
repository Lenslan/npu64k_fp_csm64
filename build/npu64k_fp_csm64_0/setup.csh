#!/bin/csh
setenv NCONFIG npu64k_fp_csm64_0

setenv NPU_HOME_RLS `pwd`
setenv NPU_DEPS_RLS ${NPU_HOME_RLS}/npu_deps
setenv NCORES_HOST `grep -c '^processor' /proc/cpuinfo`
if (! ${?NPU_RTL_SIMULATOR} ) then
    setenv NPU_RTL_SIMULATOR 0
endif

# vcs
if ( ${NPU_RTL_SIMULATOR} == 0 ) then
  which vcs >& /dev/null
  if ( $? != 0 ) then
      echo "ERROR: vcs cannot be found in ${PATH}"
  endif
  
  if (! ${?SYNOPSYS} ) then
      echo "ERROR: \$SYNOPSYS cannot be found in the environment"
  endif
endif

# xcelium
if ( ${NPU_RTL_SIMULATOR} == 1 ) then
  which xrun >& /dev/null
  if ( $? != 0 ) then
      echo "ERROR: xrun cannot be found in ${PATH}"
  endif
  
  if (! ${?SYNOPSYS} ) then
      echo "ERROR: \$SYNOPSYS cannot be found in the environment"
  endif
  setenv LD_LIBRARY_PATH "${LD_LIBRARY_PATH}:${VERDI_HOME}/share/PLI/IUS/LINUX64/boot:${VERDI_HOME}/share/PLI/IUS/LINUX64"
  
  ## For simulations with MDB connected
  #if ( ${?ARCHITECT_ROOT} ) then
  #    if ( -f "$ARCHITECT_ROOT/lib/linux_x86_64/libarc-vcs-pli-verilog.so" ) then
  #        setenv NPU_VCS_PLI $ARCHITECT_ROOT/lib/linux_x86_64
  #    endif
  #endif
  #if ( ! ${?NPU_VCS_PLI} ) then
  #    setenv NPU_VCS_PLI $NPU_HOME_RLS/lib
  #endif
  #if (! ${?LD_LIBRARY_PATH} ) then
  #    setenv LD_LIBRARY_PATH $NPU_VCS_PLI
  #else
  #    setenv LD_LIBRARY_PATH "${NPU_VCS_PLI}:${LD_LIBRARY_PATH}"
  #endif

endif

# For simulations with MDB connected
if ( ${?ARCHITECT_ROOT} ) then
    if ( -f "$ARCHITECT_ROOT/lib/linux_x86_64/libarc-vcs-pli-verilog.so" ) then
        setenv NPU_VCS_PLI $ARCHITECT_ROOT/lib/linux_x86_64
    endif
endif
if ( ! ${?NPU_VCS_PLI} ) then
    setenv NPU_VCS_PLI $NPU_HOME_RLS/lib
endif
if (! ${?LD_LIBRARY_PATH} ) then
    setenv LD_LIBRARY_PATH $NPU_VCS_PLI
else
    setenv LD_LIBRARY_PATH "${NPU_VCS_PLI}:${LD_LIBRARY_PATH}"
endif
