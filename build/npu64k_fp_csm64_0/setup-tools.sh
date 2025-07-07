#!/usr/bin/env bash
# This script is used to configure tools for validation of the release package
# inside the Synopsys network.
set +o pipefail
fs=`cat build_config.mk | grep NCONFIG | head -n1 | grep fs | wc -l`
set -o pipefail
#fs=${1:-0}

module purge

#tools for FS release validation
if [[ $fs -ne 0 ]]; then
  module load mwdt/2022.12 syn/2022.03-SP5 rtla/2022.03-SP2 verdi/2022.06-SP2
  #- load mw for DC topo syn
  #module load mw/2022.03-SP5
else
  module load mwdt syn/2022.03-SP5 rtla/2022.03-SP2 verdi
fi
module load tcl/8.6.4 gmake/3.82 
#GCC: 9.2.0 C++17
#module load gcc/9.2.0
export QSC_VER=/home/jjt/opt/ARC_2023/VCS_GNU_linux_gcc_default/linux/gcc-9.2.0
export PATH="${QSC_VER}/bin:${QSC_VER}/binutils/bin:${QSC_VER}/GCC/bin:$PATH"
export LD_LIBRARY_PATH="$QSC_VER/GCC/lib64:$LD_LIBRARY_PATH"

# VCS
if [[ -z "$NPU_RTL_SIMULATOR" || $NPU_RTL_SIMULATOR -eq 0 ]]; then
  if [[ $fs -ne 0 ]]; then
    module load vcs/2022.06-SP2
  else
    module load vcs
  fi
  echo "Environment configured for VCS simulation"
fi

# Xcelium
if [[ $NPU_RTL_SIMULATOR -eq 1 ]]; then
  export LM_LICENSE_FILE=5280@us01dwcdns000:$LM_LICENSE_FILE
  module load xcelium
  echo "Environment configured for Xcelium simulation"
fi

# Questasim / Modelsim
if [[ $NPU_RTL_SIMULATOR -eq 2 ]]; then
  export LM_LICENSE_FILE=1924@us01dwment000:$LM_LICENSE_FILE
  module load questasim
  echo "Environment configured for Questasim simulation"
fi

module list
echo "PATH: ${PATH}"
echo "FS  : $fs"
echo "GCC : `which gcc`"
echo "Make: `which make`"

